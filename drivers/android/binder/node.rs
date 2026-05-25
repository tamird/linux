// SPDX-License-Identifier: GPL-2.0

// Copyright (C) 2025 Google LLC.

use kernel::{
    list::{AtomicTracker, List, ListArc, ListLinks, TryNewListArc},
    prelude::*,
    rbtree::{RBTree, RBTreeNodeReservation},
    seq_file::SeqFile,
    seq_print,
    sync::atomic::{ordering::Relaxed, Atomic},
    sync::lock::{spinlock::SpinLockBackend, Guard},
    sync::{Arc, LockedBy, SpinLock},
    task::Kuid,
};

use crate::{
    defs::*,
    error::BinderError,
    process::{NodeRefInfo, Process, ProcessInner},
    thread::Thread,
    transaction::{Transaction, TransactionInfo},
    BinderReturnWriter, DArc, DLArc, DTRWrap, DeliverToRead,
};

use core::mem;

mod wrapper;
pub(crate) use self::wrapper::CritIncrWrapper;

#[derive(Debug)]
pub(crate) struct CouldNotDeliverCriticalIncrement;

/// Keeps track of how this node is scheduled.
///
/// There are two ways to schedule a node to a work list. Just schedule the node itself, or
/// allocate a wrapper that references the node and schedule the wrapper. These wrappers exists to
/// make it possible to "move" a node from one list to another - when `do_work` is called directly
/// on the `Node`, then it's a no-op if there's also a pending wrapper.
///
/// Wrappers are generally only needed for zero-to-one refcount increments, and there are two cases
/// of this: weak increments and strong increments. We call such increments "critical" because it
/// is critical that they are delivered to the thread doing the increment. Some examples:
///
/// * One thread makes a zero-to-one strong increment, and another thread makes a zero-to-one weak
///   increment. Delivering the node to the thread doing the weak increment is wrong, since the
///   thread doing the strong increment may have ended a long time ago when the command is actually
///   processed by userspace.
///
/// * We have a weak reference and are about to drop it on one thread. But then another thread does
///   a zero-to-one strong increment. If the strong increment gets sent to the thread that was
///   about to drop the weak reference, then the strong increment could be processed after the
///   other thread has already exited, which would be too late.
///
/// Note that trying to create a `ListArc` to the node can succeed even if `has_normal_push` is
/// set. This is because another thread might just have popped the node from a todo list, but not
/// yet called `do_work`. However, if `has_normal_push` is false, then creating a `ListArc` should
/// always succeed.
///
/// Like the other fields in `NodeInner`, the delivery state is protected by the process lock.
struct DeliveryState {
    /// Is the `Node` currently scheduled?
    has_pushed_node: bool,

    /// Is a wrapper currently scheduled?
    ///
    /// The wrapper is used only for strong zero2one increments.
    has_pushed_wrapper: bool,

    /// Is the currently scheduled `Node` scheduled due to a weak zero2one increment?
    ///
    /// Weak zero2one operations are always scheduled using the `Node`.
    has_weak_zero2one: bool,

    /// Is the currently scheduled wrapper/`Node` scheduled due to a strong zero2one increment?
    ///
    /// If `has_pushed_wrapper` is set, then the strong zero2one increment was scheduled using the
    /// wrapper. Otherwise, `has_pushed_node` must be set and it was scheduled using the `Node`.
    has_strong_zero2one: bool,
}

impl DeliveryState {
    fn should_normal_push(&self) -> bool {
        !self.has_pushed_node && !self.has_pushed_wrapper
    }

    fn did_normal_push(&mut self) {
        assert!(self.should_normal_push());
        self.has_pushed_node = true;
    }

    fn should_push_weak_zero2one(&self) -> bool {
        !self.has_weak_zero2one && !self.has_strong_zero2one
    }

    fn can_push_weak_zero2one_normally(&self) -> bool {
        !self.has_pushed_node
    }

    fn did_push_weak_zero2one(&mut self) {
        assert!(self.should_push_weak_zero2one());
        assert!(self.can_push_weak_zero2one_normally());
        self.has_pushed_node = true;
        self.has_weak_zero2one = true;
    }

    fn should_push_strong_zero2one(&self) -> bool {
        !self.has_strong_zero2one
    }

    fn can_push_strong_zero2one_normally(&self) -> bool {
        !self.has_pushed_node
    }

    fn did_push_strong_zero2one(&mut self) {
        assert!(self.should_push_strong_zero2one());
        assert!(self.can_push_strong_zero2one_normally());
        self.has_pushed_node = true;
        self.has_strong_zero2one = true;
    }

    fn did_push_strong_zero2one_wrapper(&mut self) {
        assert!(self.should_push_strong_zero2one());
        assert!(!self.can_push_strong_zero2one_normally());
        self.has_pushed_wrapper = true;
        self.has_strong_zero2one = true;
    }
}

struct CountState {
    /// The reference count.
    count: usize,
    /// Whether the process that owns this node thinks that we hold a refcount on it. (Note that
    /// even if count is greater than one, we only increment it once in the owning process.)
    has_count: bool,
}

impl CountState {
    fn new() -> Self {
        Self {
            count: 0,
            has_count: false,
        }
    }
}

struct NodeInner {
    /// Strong refcounts held on this node by `NodeRef` objects.
    strong: CountState,
    /// Weak refcounts held on this node by `NodeRef` objects.
    weak: CountState,
    delivery_state: DeliveryState,
    /// The binder driver guarantees that oneway transactions sent to the same node are serialized,
    /// that is, userspace will not be given the next one until it has finished processing the
    /// previous oneway transaction. This is done to avoid the case where two oneway transactions
    /// arrive in opposite order from the order in which they were sent. (E.g., they could be
    /// delivered to two different threads, which could appear as-if they were sent in opposite
    /// order.)
    ///
    /// To fix that, we store pending oneway transactions in a separate list in the node, and don't
    /// deliver the next oneway transaction until userspace signals that it has finished processing
    /// the previous oneway transaction by calling the `BC_FREE_BUFFER` ioctl.
    oneway_todo: List<DTRWrap<Transaction>>,
    /// Keeps track of whether this node has a pending oneway transaction.
    ///
    /// When this is true, incoming oneway transactions are stored in `oneway_todo`, instead of
    /// being delivered directly to the process.
    has_oneway_transaction: bool,
    /// List of processes to deliver a notification to when this node is destroyed (usually due to
    /// the process dying).
    death_list: List<DTRWrap<NodeDeath>, 1>,
    /// List of processes to deliver freeze notifications to.
    freeze_list: KVVec<Arc<Process>>,
    /// The number of active BR_INCREFS or BR_ACQUIRE operations. (should be maximum two)
    ///
    /// If this is non-zero, then we postpone any BR_RELEASE or BR_DECREFS notifications until the
    /// active operations have ended. This avoids the situation an increment and decrement get
    /// reordered from userspace's perspective.
    active_inc_refs: u8,
    /// List of `NodeRefInfo` objects that reference this node.
    refs: List<NodeRefInfo, { NodeRefInfo::LIST_NODE }>,
    multiplexed_requests: RBTree<u64, MultiplexedRequest>,
    multiplexed_claims: List<DTRWrap<MultiplexedClaimWork>, 1>,
    next_multiplexed_request: u64,
    next_multiplexed_terminal: u64,
    multiplexed_retired: bool,
}

const MAX_PENDING_MULTIPLEXED_REQUESTS: usize = 1024;
const MAX_PENDING_MULTIPLEXED_REPLY_BYTES: usize = kernel::bindings::SZ_4M as usize;

enum MultiplexedTerminal {
    Reply(MultiplexedReplyPayload),
    Error { reason: u32, error: i32 },
}

impl MultiplexedTerminal {
    fn reply_bytes(&self) -> usize {
        match self {
            Self::Reply(reply) => reply.data.len(),
            Self::Error { .. } => 0,
        }
    }
}

enum MultiplexedRequestState {
    Pending,
    ReplyReserved {
        bytes: usize,
    },
    Ready {
        sequence: u64,
        terminal: MultiplexedTerminal,
    },
    Claimed {
        sequence: u64,
    },
}

struct MultiplexedRequest {
    request_id: u64,
    state: MultiplexedRequestState,
}

pub(crate) struct MultiplexedReplyPayload {
    code: u32,
    flags: u32,
    data: KVec<u8>,
    sender_euid: Kuid,
}

impl MultiplexedReplyPayload {
    pub(crate) fn new(code: u32, flags: u32, data: KVec<u8>) -> Self {
        Self {
            code,
            flags,
            data,
            sender_euid: Kuid::current_euid(),
        }
    }
}

use kernel::bindings::rb_node_layout;
use mem::offset_of;
pub(crate) const NODE_LAYOUT: rb_node_layout = rb_node_layout {
    arc_offset: Arc::<Node>::DATA_OFFSET + offset_of!(DTRWrap<Node>, wrapped),
    debug_id: offset_of!(Node, debug_id),
    ptr: offset_of!(Node, ptr),
};

#[pin_data]
pub(crate) struct Node {
    pub(crate) debug_id: usize,
    ptr: u64,
    pub(crate) cookie: u64,
    pub(crate) flags: u32,
    pub(crate) owner: Arc<Process>,
    inner: LockedBy<NodeInner, ProcessInner>,
    #[pin]
    links_track: AtomicTracker,
}

kernel::list::impl_list_arc_safe! {
    impl ListArcSafe<0> for Node {
        tracked_by links_track: AtomicTracker;
    }
}

// Make `oneway_todo` work.
kernel::list::impl_list_item! {
    impl ListItem<0> for DTRWrap<Transaction> {
        using ListLinks { self.links.inner };
    }
}

impl Node {
    pub(crate) fn new(
        ptr: u64,
        cookie: u64,
        flags: u32,
        owner: Arc<Process>,
    ) -> impl PinInit<Self> {
        pin_init!(Self {
            inner: LockedBy::new(
                &owner.inner,
                NodeInner {
                    strong: CountState::new(),
                    weak: CountState::new(),
                    delivery_state: DeliveryState {
                        has_pushed_node: false,
                        has_pushed_wrapper: false,
                        has_weak_zero2one: false,
                        has_strong_zero2one: false,
                    },
                    death_list: List::new(),
                    oneway_todo: List::new(),
                    freeze_list: KVVec::new(),
                    has_oneway_transaction: false,
                    active_inc_refs: 0,
                    refs: List::new(),
                    multiplexed_requests: RBTree::new(),
                    multiplexed_claims: List::new(),
                    next_multiplexed_request: 0,
                    next_multiplexed_terminal: 0,
                    multiplexed_retired: false,
                },
            ),
            debug_id: super::next_debug_id(),
            ptr,
            cookie,
            flags,
            owner,
            links_track <- AtomicTracker::new(),
        })
    }

    pub(crate) fn has_oneway_transaction(&self, owner_inner: &mut ProcessInner) -> bool {
        let inner = self.inner.access_mut(owner_inner);
        inner.has_oneway_transaction
    }

    #[inline(never)]
    pub(crate) fn full_debug_print(
        &self,
        m: &SeqFile,
        owner_inner: &mut ProcessInner,
    ) -> Result<()> {
        let inner = self.inner.access_mut(owner_inner);
        seq_print!(
            m,
            "  node {}: u{:016x} c{:016x} hs {} hw {} cs {} cw {}",
            self.debug_id,
            self.ptr,
            self.cookie,
            inner.strong.has_count,
            inner.weak.has_count,
            inner.strong.count,
            inner.weak.count,
        );
        if !inner.refs.is_empty() {
            seq_print!(m, " proc");
            for node_ref in &inner.refs {
                seq_print!(m, " {}", node_ref.process.task.pid());
            }
        }
        seq_print!(m, "\n");
        for t in &inner.oneway_todo {
            t.debug_print_inner(m, "    pending async transaction ");
        }
        Ok(())
    }

    /// Insert the `NodeRef` into this `refs` list.
    ///
    /// # Safety
    ///
    /// It must be the case that `info.node_ref.node` is this node.
    pub(crate) unsafe fn insert_node_info(
        &self,
        info: ListArc<NodeRefInfo, { NodeRefInfo::LIST_NODE }>,
    ) {
        self.inner
            .access_mut(&mut self.owner.inner.lock())
            .refs
            .push_front(info);
    }

    /// Insert the `NodeRef` into this `refs` list.
    ///
    /// # Safety
    ///
    /// It must be the case that `info.node_ref.node` is this node.
    pub(crate) unsafe fn remove_node_info(
        &self,
        info: &NodeRefInfo,
    ) -> Option<ListArc<NodeRefInfo, { NodeRefInfo::LIST_NODE }>> {
        // SAFETY: We always insert `NodeRefInfo` objects into the `refs` list of the node that it
        // references in `info.node_ref.node`. That is this node, so `info` cannot possibly be in
        // the `refs` list of another node.
        unsafe {
            self.inner
                .access_mut(&mut self.owner.inner.lock())
                .refs
                .remove(info)
        }
    }

    /// An id that is unique across all binder nodes on the system. Used as the key in the
    /// `by_node` map.
    pub(crate) fn global_id(&self) -> usize {
        self as *const Node as usize
    }

    pub(crate) fn get_id(&self) -> (u64, u64) {
        (self.ptr, self.cookie)
    }

    pub(crate) fn uses_multiplexed_delivery(&self) -> bool {
        self.flags & FLAT_BINDER_FLAG_MULTIPLEXED_DELIVERY != 0
    }

    pub(crate) fn is_multiplexed_retired(
        &self,
        guard: &Guard<'_, ProcessInner, SpinLockBackend>,
    ) -> bool {
        self.inner.access(guard).multiplexed_retired
    }

    pub(crate) fn accept_multiplexed_request(&self, request_id: u64) -> Result<u64> {
        let reservation = RBTreeNodeReservation::new(GFP_KERNEL)?;
        let mut guard = self.owner.inner.lock();
        if guard.is_dead {
            return Err(ESRCH);
        }
        let inner = self.inner.access_mut(&mut guard);
        if inner.multiplexed_retired {
            return Err(ESRCH);
        }
        if inner.multiplexed_requests.iter().count() >= MAX_PENDING_MULTIPLEXED_REQUESTS {
            return Err(ENOSPC);
        }
        let key = inner
            .next_multiplexed_request
            .checked_add(1)
            .ok_or(ENOSPC)?;
        inner.next_multiplexed_request = key;
        inner.multiplexed_requests.insert(reservation.into_node(
            key,
            MultiplexedRequest {
                request_id,
                state: MultiplexedRequestState::Pending,
            },
        ));
        Ok(key)
    }

    pub(crate) fn can_issue_multiplexed_reply(
        &self,
        key: u64,
        guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
    ) -> bool {
        let inner = self.inner.access_mut(guard);
        !inner.multiplexed_retired
            && matches!(
                inner
                    .multiplexed_requests
                    .get(&key)
                    .map(|request| &request.state),
                Some(MultiplexedRequestState::Pending)
            )
    }

    pub(crate) fn fail_multiplexed_request(&self, key: u64, reason: u32, error: i32) {
        {
            let mut guard = self.owner.inner.lock();
            let reserved = {
                let inner = self.inner.access_mut(&mut guard);
                match inner.multiplexed_requests.get(&key).map(|r| &r.state) {
                    Some(MultiplexedRequestState::Pending) => 0,
                    Some(MultiplexedRequestState::ReplyReserved { bytes }) => *bytes,
                    _ => return,
                }
            };
            guard.multiplexed_reply_bytes -= reserved;
            let inner = self.inner.access_mut(&mut guard);
            inner.next_multiplexed_terminal = inner.next_multiplexed_terminal.wrapping_add(1);
            let sequence = inner.next_multiplexed_terminal;
            inner.multiplexed_requests.get_mut(&key).unwrap().state =
                MultiplexedRequestState::Ready {
                    sequence,
                    terminal: MultiplexedTerminal::Error { reason, error },
                };
        }
        self.dispatch_multiplexed_claims();
    }

    pub(crate) fn reserve_multiplexed_reply_payload(
        &self,
        key: u64,
        size: usize,
        guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
    ) -> Result {
        {
            let inner = self.inner.access_mut(guard);
            if !matches!(
                inner.multiplexed_requests.get(&key).map(|r| &r.state),
                Some(MultiplexedRequestState::Pending)
            ) {
                return Err(ESRCH);
            }
        }
        if guard
            .multiplexed_reply_bytes
            .checked_add(size)
            .is_none_or(|bytes| bytes > MAX_PENDING_MULTIPLEXED_REPLY_BYTES)
        {
            return Err(ENOSPC);
        }
        guard.multiplexed_reply_bytes += size;
        let inner = self.inner.access_mut(guard);
        inner.multiplexed_requests.get_mut(&key).unwrap().state =
            MultiplexedRequestState::ReplyReserved { bytes: size };
        Ok(())
    }

    pub(crate) fn cancel_multiplexed_reply_payload(
        &self,
        key: u64,
        guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
    ) {
        let bytes = {
            let inner = self.inner.access_mut(guard);
            let Some(MultiplexedRequestState::ReplyReserved { bytes }) = inner
                .multiplexed_requests
                .get(&key)
                .map(|request| &request.state)
            else {
                return;
            };
            *bytes
        };
        guard.multiplexed_reply_bytes -= bytes;
        let inner = self.inner.access_mut(guard);
        inner.multiplexed_requests.get_mut(&key).unwrap().state = MultiplexedRequestState::Pending;
    }

    pub(crate) fn queue_multiplexed_reply(
        &self,
        key: u64,
        reply: MultiplexedReplyPayload,
        guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
    ) -> Result {
        let inner = self.inner.access_mut(guard);
        if !matches!(
            inner.multiplexed_requests.get(&key).map(|r| &r.state),
            Some(MultiplexedRequestState::ReplyReserved { bytes }) if *bytes == reply.data.len()
        ) {
            return Err(ESRCH);
        }
        inner.next_multiplexed_terminal = inner.next_multiplexed_terminal.wrapping_add(1);
        let sequence = inner.next_multiplexed_terminal;
        inner.multiplexed_requests.get_mut(&key).unwrap().state = MultiplexedRequestState::Ready {
            sequence,
            terminal: MultiplexedTerminal::Reply(reply),
        };
        Ok(())
    }

    pub(crate) fn claim_multiplexed_reply(
        self: &DArc<Self>,
        recipient: Arc<Process>,
        claim_id: u64,
    ) -> Result {
        let work = MultiplexedClaimWork::try_new(self.clone(), recipient.clone(), claim_id)?;
        let node_work: ListArc<DTRWrap<MultiplexedClaimWork>, 1> =
            ListArc::<DTRWrap<MultiplexedClaimWork>, 1>::try_from_arc(work.clone())
                .ok()
                .unwrap();
        let recipient_work: ListArc<DTRWrap<MultiplexedClaimWork>, 2> =
            ListArc::<DTRWrap<MultiplexedClaimWork>, 2>::try_from_arc(work)
                .ok()
                .unwrap();
        if Arc::ptr_eq(&recipient, &self.owner) {
            let mut guard = self.owner.inner.lock();
            if guard.is_dead {
                return Err(ESRCH);
            }
            let inner = self.inner.access_mut(&mut guard);
            if inner.multiplexed_retired {
                return Err(ESRCH);
            }
            if inner.multiplexed_claims.iter().count()
                >= inner
                    .multiplexed_requests
                    .values()
                    .filter(|request| {
                        matches!(
                            request.state,
                            MultiplexedRequestState::Pending
                                | MultiplexedRequestState::ReplyReserved { .. }
                                | MultiplexedRequestState::Ready { .. }
                        )
                    })
                    .count()
            {
                return Err(ENOSPC);
            }
            inner.multiplexed_claims.push_back(node_work);
            guard.pending_multiplexed_claims.push_back(recipient_work);
        } else {
            let register = |owner_guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
                            recipient_guard: &mut Guard<'_, ProcessInner, SpinLockBackend>|
             -> Result {
                if owner_guard.is_dead || recipient_guard.is_dead {
                    return Err(ESRCH);
                }
                let inner = self.inner.access_mut(owner_guard);
                if inner.multiplexed_retired {
                    return Err(ESRCH);
                }
                if inner.multiplexed_claims.iter().count()
                    >= inner
                        .multiplexed_requests
                        .values()
                        .filter(|request| {
                            matches!(
                                request.state,
                                MultiplexedRequestState::Pending
                                    | MultiplexedRequestState::ReplyReserved { .. }
                                    | MultiplexedRequestState::Ready { .. }
                            )
                        })
                        .count()
                {
                    return Err(ENOSPC);
                }
                inner.multiplexed_claims.push_back(node_work);
                recipient_guard
                    .pending_multiplexed_claims
                    .push_back(recipient_work);
                Ok(())
            };
            // Transferred nodes permit reciprocal claims between endpoints.
            // Use a stable order whenever two endpoint locks are needed.
            if Arc::as_ptr(&recipient) < Arc::as_ptr(&self.owner) {
                let mut recipient_guard = recipient.inner.lock();
                let mut owner_guard = self.owner.inner.lock();
                register(&mut owner_guard, &mut recipient_guard)?;
            } else {
                let mut owner_guard = self.owner.inner.lock();
                let mut recipient_guard = recipient.inner.lock();
                register(&mut owner_guard, &mut recipient_guard)?;
            }
        }
        self.dispatch_multiplexed_claims();
        Ok(())
    }

    fn cancel_multiplexed_claim(&self, claim: &DArc<MultiplexedClaimWork>) {
        let removed = {
            let mut guard = self.owner.inner.lock();
            // SAFETY: A claim is inserted only in the pending-claim list of its node.
            unsafe {
                self.inner
                    .access_mut(&mut guard)
                    .multiplexed_claims
                    .remove(claim)
            }
        };
        drop(removed);
    }

    fn requeue_multiplexed_terminal(&self, key: u64, terminal: MultiplexedTerminal) {
        let reply_bytes = terminal.reply_bytes();
        let mut guard = self.owner.inner.lock();
        let release_bytes = {
            let inner = self.inner.access_mut(&mut guard);
            if inner.multiplexed_retired {
                match inner.multiplexed_requests.get(&key).map(|r| &r.state) {
                    Some(MultiplexedRequestState::Claimed { .. }) => {
                        inner.multiplexed_requests.remove(&key);
                        true
                    }
                    None => true,
                    _ => false,
                }
            } else {
                let sequence = match inner.multiplexed_requests.get(&key).map(|r| &r.state) {
                    Some(MultiplexedRequestState::Claimed { sequence, .. }) => *sequence,
                    _ => return,
                };
                inner.multiplexed_requests.get_mut(&key).unwrap().state =
                    MultiplexedRequestState::Ready { sequence, terminal };
                return;
            }
        };
        if release_bytes {
            guard.multiplexed_reply_bytes -= reply_bytes;
        }
    }

    pub(crate) fn dispatch_multiplexed_claims(&self) {
        loop {
            let claimed = {
                let mut guard = self.owner.inner.lock();
                let inner = self.inner.access_mut(&mut guard);
                let Some(work) = inner.multiplexed_claims.pop_front() else {
                    return;
                };
                let mut ready = None;
                for (key, request) in inner.multiplexed_requests.iter() {
                    if let MultiplexedRequestState::Ready { sequence, .. } = request.state {
                        if ready.is_none_or(|(_, old)| sequence < old) {
                            ready = Some((*key, sequence));
                        }
                    }
                }
                let Some((key, sequence)) = ready else {
                    inner.multiplexed_claims.push_front(work);
                    return;
                };
                let request = inner.multiplexed_requests.get_mut(&key).unwrap();
                let state = mem::replace(
                    &mut request.state,
                    MultiplexedRequestState::Claimed { sequence },
                );
                if let MultiplexedRequestState::Ready { terminal, .. } = state {
                    work.set_claim(key, request.request_id, terminal);
                    Some((work.recipient.clone(), work.into_arc()))
                } else {
                    None
                }
            };
            let Some((recipient, work)) = claimed else {
                continue;
            };
            recipient.remove_multiplexed_claim(&work);
            let work: DLArc<dyn DeliverToRead> = ListArc::try_from_arc(work).ok().unwrap();
            let _ = recipient.push_work(work);
        }
    }

    fn complete_multiplexed_claim(&self, key: u64, reply_bytes: usize) {
        let mut guard = self.owner.inner.lock();
        let (completed, remove_node) = {
            let inner = self.inner.access_mut(&mut guard);
            let completed = if matches!(
                inner.multiplexed_requests.get(&key).map(|r| &r.state),
                Some(MultiplexedRequestState::Claimed { .. })
            ) {
                inner.multiplexed_requests.remove(&key);
                true
            } else if inner.multiplexed_retired && inner.multiplexed_requests.get(&key).is_none()
            {
                true
            } else {
                false
            };
            let remove_node = completed
                && inner.multiplexed_requests.is_empty()
                && inner.multiplexed_claims.is_empty()
                && inner.active_inc_refs == 0
                && inner.strong.count == 0
                && inner.weak.count == 0
                && !inner.strong.has_count
                && !inner.weak.has_count;
            (completed, remove_node)
        };
        if completed {
            guard.multiplexed_reply_bytes -= reply_bytes;
        }
        if remove_node {
            guard.remove_node(self.ptr);
        }
    }

    pub(crate) fn add_death(
        &self,
        death: ListArc<DTRWrap<NodeDeath>, 1>,
        guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
    ) {
        self.inner.access_mut(guard).death_list.push_back(death);
    }

    pub(crate) fn inc_ref_done_locked(
        self: &DArc<Node>,
        _strong: bool,
        owner_inner: &mut ProcessInner,
    ) -> Option<DLArc<Node>> {
        let inner = self.inner.access_mut(owner_inner);
        if inner.active_inc_refs == 0 {
            pr_err!("inc_ref_done called when no active inc_refs");
            return None;
        }

        inner.active_inc_refs -= 1;
        if inner.active_inc_refs == 0 {
            // Having active inc_refs can inhibit dropping of ref-counts. Calculate whether we
            // would send a refcount decrement, and if so, tell the caller to schedule us.
            let strong = inner.strong.count > 0;
            let has_strong = inner.strong.has_count;
            let weak = strong || inner.weak.count > 0;
            let has_weak = inner.weak.has_count;

            let should_drop_weak = !weak && has_weak;
            let should_drop_strong = !strong && has_strong;

            // If we want to drop the ref-count again, tell the caller to schedule a work node for
            // that.
            let need_push = should_drop_weak || should_drop_strong;

            if need_push && inner.delivery_state.should_normal_push() {
                let list_arc = ListArc::try_from_arc(self.clone()).ok().unwrap();
                inner.delivery_state.did_normal_push();
                Some(list_arc)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub(crate) fn update_refcount_locked(
        self: &DArc<Node>,
        inc: bool,
        strong: bool,
        count: usize,
        owner_inner: &mut ProcessInner,
    ) -> Option<DLArc<Node>> {
        let is_dead = owner_inner.is_dead;
        let inner = self.inner.access_mut(owner_inner);

        // Get a reference to the state we'll update.
        let state = if strong {
            &mut inner.strong
        } else {
            &mut inner.weak
        };

        // Update the count and determine whether we need to push work.
        let need_push = if inc {
            state.count += count;
            // TODO: This method shouldn't be used for zero-to-one increments.
            !is_dead && !state.has_count
        } else {
            if state.count < count {
                pr_err!("Failure: refcount underflow!");
                return None;
            }
            state.count -= count;
            !is_dead && state.count == 0 && state.has_count
        };

        if need_push && inner.delivery_state.should_normal_push() {
            let list_arc = ListArc::try_from_arc(self.clone()).ok().unwrap();
            inner.delivery_state.did_normal_push();
            Some(list_arc)
        } else {
            None
        }
    }

    pub(crate) fn incr_refcount_allow_zero2one(
        self: &DArc<Self>,
        strong: bool,
        owner_inner: &mut ProcessInner,
    ) -> Result<Option<DLArc<Node>>, CouldNotDeliverCriticalIncrement> {
        let is_dead = owner_inner.is_dead;
        let inner = self.inner.access_mut(owner_inner);

        // Get a reference to the state we'll update.
        let state = if strong {
            &mut inner.strong
        } else {
            &mut inner.weak
        };

        // Update the count and determine whether we need to push work.
        state.count += 1;
        if is_dead || state.has_count {
            return Ok(None);
        }

        // Userspace needs to be notified of this.
        if !strong && inner.delivery_state.should_push_weak_zero2one() {
            assert!(inner.delivery_state.can_push_weak_zero2one_normally());
            let list_arc = ListArc::try_from_arc(self.clone()).ok().unwrap();
            inner.delivery_state.did_push_weak_zero2one();
            Ok(Some(list_arc))
        } else if strong && inner.delivery_state.should_push_strong_zero2one() {
            if inner.delivery_state.can_push_strong_zero2one_normally() {
                let list_arc = ListArc::try_from_arc(self.clone()).ok().unwrap();
                inner.delivery_state.did_push_strong_zero2one();
                Ok(Some(list_arc))
            } else {
                state.count -= 1;
                Err(CouldNotDeliverCriticalIncrement)
            }
        } else {
            // Work is already pushed, and we don't need to push again.
            Ok(None)
        }
    }

    pub(crate) fn incr_refcount_allow_zero2one_with_wrapper(
        self: &DArc<Self>,
        strong: bool,
        wrapper: CritIncrWrapper,
        owner_inner: &mut ProcessInner,
    ) -> Option<DLArc<dyn DeliverToRead>> {
        match self.incr_refcount_allow_zero2one(strong, owner_inner) {
            Ok(Some(node)) => Some(node as _),
            Ok(None) => None,
            Err(CouldNotDeliverCriticalIncrement) => {
                assert!(strong);
                let inner = self.inner.access_mut(owner_inner);
                inner.strong.count += 1;
                inner.delivery_state.did_push_strong_zero2one_wrapper();
                Some(wrapper.init(self.clone()))
            }
        }
    }

    pub(crate) fn update_refcount(self: &DArc<Self>, inc: bool, count: usize, strong: bool) {
        self.owner
            .inner
            .lock()
            .update_node_refcount(self, inc, strong, count, None);
    }

    pub(crate) fn populate_counts(
        &self,
        out: &mut BinderNodeInfoForRef,
        guard: &Guard<'_, ProcessInner, SpinLockBackend>,
    ) {
        let inner = self.inner.access(guard);
        out.strong_count = inner.strong.count as _;
        out.weak_count = inner.weak.count as _;
    }

    pub(crate) fn populate_debug_info(
        &self,
        out: &mut BinderNodeDebugInfo,
        guard: &Guard<'_, ProcessInner, SpinLockBackend>,
    ) {
        out.ptr = self.ptr as _;
        out.cookie = self.cookie as _;
        let inner = self.inner.access(guard);
        if inner.strong.has_count {
            out.has_strong_ref = 1;
        }
        if inner.weak.has_count {
            out.has_weak_ref = 1;
        }
    }

    pub(crate) fn force_has_count(&self, guard: &mut Guard<'_, ProcessInner, SpinLockBackend>) {
        let inner = self.inner.access_mut(guard);
        inner.strong.has_count = true;
        inner.weak.has_count = true;
    }

    fn write(&self, writer: &mut BinderReturnWriter<'_>, code: u32) -> Result {
        writer.write_code(code)?;
        writer.write_payload(&self.ptr)?;
        writer.write_payload(&self.cookie)?;
        Ok(())
    }

    pub(crate) fn submit_oneway(
        &self,
        transaction: DLArc<Transaction>,
        guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
    ) -> Result<(), (BinderError, DLArc<dyn DeliverToRead>)> {
        if guard.is_dead {
            return Err((BinderError::new_dead(), transaction));
        }

        let inner = self.inner.access_mut(guard);
        if inner.has_oneway_transaction {
            inner.oneway_todo.push_back(transaction);
        } else {
            inner.has_oneway_transaction = true;
            guard.push_work(transaction)?;
        }
        Ok(())
    }

    pub(crate) fn retire_multiplexed_node(&self, reason: u32) {
        let mut guard = self.owner.inner.lock();
        let reserved_bytes = {
            let inner = self.inner.access_mut(&mut guard);
            inner.multiplexed_retired = true;
            let mut reserved_bytes = 0;
            let mut sequence = inner.next_multiplexed_terminal;
            for request in inner.multiplexed_requests.values_mut() {
                let bytes = match request.state {
                    MultiplexedRequestState::Pending => Some(0),
                    MultiplexedRequestState::ReplyReserved { bytes } => Some(bytes),
                    _ => None,
                };
                if let Some(bytes) = bytes {
                    reserved_bytes += bytes;
                    sequence = sequence.wrapping_add(1);
                    request.state = MultiplexedRequestState::Ready {
                        sequence,
                        terminal: MultiplexedTerminal::Error { reason, error: 0 },
                    };
                }
            }
            inner.next_multiplexed_terminal = sequence;
            reserved_bytes
        };
        guard.multiplexed_reply_bytes -= reserved_bytes;
        drop(guard);
        self.owner
            .invalidate_multiplexed_reply_tokens_for_node(self.global_id());
        loop {
            let work = {
                let mut guard = self.owner.inner.lock();
                self.inner.access_mut(&mut guard).oneway_todo.pop_front()
            };
            let Some(work) = work else {
                break;
            };
            work.into_arc().cancel();
        }
        self.dispatch_multiplexed_claims();
        let mut guard = self.owner.inner.lock();
        let reply_bytes = {
            let inner = self.inner.access_mut(&mut guard);
            let reply_bytes = inner
                .multiplexed_requests
                .values()
                .map(|request| match &request.state {
                    MultiplexedRequestState::Ready { terminal, .. } => terminal.reply_bytes(),
                    MultiplexedRequestState::ReplyReserved { bytes } => *bytes,
                    // Queued terminal work releases its charge when consumed or canceled.
                    MultiplexedRequestState::Claimed { .. } => 0,
                    MultiplexedRequestState::Pending => 0,
                })
                .sum::<usize>();
            inner.multiplexed_requests = RBTree::new();
            reply_bytes
        };
        guard.multiplexed_reply_bytes -= reply_bytes;
        drop(guard);
        // Recipient teardown may remove a node registration concurrently, so
        // keep removals on the original list head rather than moving it out.
        loop {
            let claim = {
                let mut guard = self.owner.inner.lock();
                self.inner
                    .access_mut(&mut guard)
                    .multiplexed_claims
                    .pop_front()
            };
            let Some(claim) = claim else {
                break;
            };
            let claim = claim.into_arc();
            claim.recipient.remove_multiplexed_claim(&claim);
        }
        let mut guard = self.owner.inner.lock();
        let remove_node = {
            let inner = self.inner.access_mut(&mut guard);
            inner.multiplexed_requests.is_empty()
                && inner.multiplexed_claims.is_empty()
                && inner.active_inc_refs == 0
                && inner.strong.count == 0
                && inner.weak.count == 0
                && !inner.strong.has_count
                && !inner.weak.has_count
        };
        if remove_node {
            guard.remove_node(self.ptr);
        }
    }

    pub(crate) fn release(&self) {
        self.retire_multiplexed_node(BINDER_MULTIPLEXED_REPLY_DEAD);
        let mut guard = self.owner.inner.lock();
        while let Some(work) = self.inner.access_mut(&mut guard).oneway_todo.pop_front() {
            drop(guard);
            work.into_arc().cancel();
            guard = self.owner.inner.lock();
        }

        while let Some(death) = self.inner.access_mut(&mut guard).death_list.pop_front() {
            drop(guard);
            death.into_arc().set_dead();
            guard = self.owner.inner.lock();
        }
    }

    pub(crate) fn pending_oneway_finished(&self) {
        let mut guard = self.owner.inner.lock();
        if guard.is_dead {
            // Cleanup will happen in `Process::deferred_release`.
            return;
        }

        let inner = self.inner.access_mut(&mut guard);
        if inner.multiplexed_retired {
            inner.has_oneway_transaction = false;
            return;
        }

        let transaction = inner.oneway_todo.pop_front();
        inner.has_oneway_transaction = transaction.is_some();
        if let Some(transaction) = transaction {
            match guard.push_work(transaction) {
                Ok(()) => {}
                Err((_err, work)) => {
                    // Process is dead.
                    // This shouldn't happen due to the `is_dead` check, but if it does, just drop
                    // the transaction and return.
                    drop(guard);
                    drop(work);
                }
            }
        }
    }

    /// Finds an outdated transaction that the given transaction can replace.
    ///
    /// If one is found, it is removed from the list and returned.
    pub(crate) fn take_outdated_transaction(
        &self,
        new: &Transaction,
        guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
    ) -> Option<DLArc<Transaction>> {
        let inner = self.inner.access_mut(guard);
        let mut cursor = inner.oneway_todo.cursor_front();
        while let Some(next) = cursor.peek_next() {
            if new.can_replace(&next) {
                return Some(next.remove());
            }
            cursor.move_next();
        }
        None
    }

    /// This is split into a separate function since it's called by both `Node::do_work` and
    /// `NodeWrapper::do_work`.
    fn do_work_locked(
        &self,
        writer: &mut BinderReturnWriter<'_>,
        mut guard: Guard<'_, ProcessInner, SpinLockBackend>,
    ) -> Result<bool> {
        let inner = self.inner.access_mut(&mut guard);
        let strong = inner.strong.count > 0;
        let has_strong = inner.strong.has_count;
        let weak = strong || inner.weak.count > 0;
        let has_weak = inner.weak.has_count;

        if weak && !has_weak {
            inner.weak.has_count = true;
            inner.active_inc_refs += 1;
        }

        if strong && !has_strong {
            inner.strong.has_count = true;
            inner.active_inc_refs += 1;
        }

        let no_active_inc_refs = inner.active_inc_refs == 0;
        let should_drop_weak = no_active_inc_refs && (!weak && has_weak);
        let should_drop_strong = no_active_inc_refs && (!strong && has_strong);
        if should_drop_weak {
            inner.weak.has_count = false;
        }
        if should_drop_strong {
            inner.strong.has_count = false;
        }
        let keep_for_multiplexed_state =
            !inner.multiplexed_requests.is_empty() || !inner.multiplexed_claims.is_empty();
        if no_active_inc_refs && !weak && !keep_for_multiplexed_state {
            // Remove the node if there are no references to it.
            guard.remove_node(self.ptr);
        }
        drop(guard);

        if weak && !has_weak {
            self.write(writer, BR_INCREFS)?;
        }
        if strong && !has_strong {
            self.write(writer, BR_ACQUIRE)?;
        }
        if should_drop_strong {
            self.write(writer, BR_RELEASE)?;
        }
        if should_drop_weak {
            self.write(writer, BR_DECREFS)?;
        }

        Ok(true)
    }

    pub(crate) fn add_freeze_listener(
        &self,
        process: &Arc<Process>,
        flags: kernel::alloc::Flags,
    ) -> Result {
        let mut vec_alloc = KVVec::<Arc<Process>>::new();
        loop {
            let mut guard = self.owner.inner.lock();
            // Do not check for `guard.dead`. The `dead` flag that matters here is the owner of the
            // listener, no the target.
            let inner = self.inner.access_mut(&mut guard);
            let len = inner.freeze_list.len();
            if len >= inner.freeze_list.capacity() {
                if len >= vec_alloc.capacity() {
                    drop(guard);
                    vec_alloc = KVVec::with_capacity((1 + len).next_power_of_two(), flags)?;
                    continue;
                }
                mem::swap(&mut inner.freeze_list, &mut vec_alloc);
                for elem in vec_alloc.drain_all() {
                    inner.freeze_list.push_within_capacity(elem)?;
                }
            }
            inner.freeze_list.push_within_capacity(process.clone())?;
            return Ok(());
        }
    }

    pub(crate) fn remove_freeze_listener(&self, p: &Arc<Process>) {
        let _unused_capacity;
        let mut guard = self.owner.inner.lock();
        let inner = self.inner.access_mut(&mut guard);
        let len = inner.freeze_list.len();
        inner.freeze_list.retain(|proc| !Arc::ptr_eq(proc, p));
        if len == inner.freeze_list.len() {
            pr_warn!(
                "Could not remove freeze listener for {}\n",
                p.pid_in_current_ns()
            );
        }
        if inner.freeze_list.is_empty() {
            _unused_capacity = mem::take(&mut inner.freeze_list);
        }
    }

    pub(crate) fn freeze_list<'a>(&'a self, guard: &'a ProcessInner) -> &'a [Arc<Process>] {
        &self.inner.access(guard).freeze_list
    }
}

impl DeliverToRead for Node {
    fn do_work(
        self: DArc<Self>,
        _thread: &Thread,
        writer: &mut BinderReturnWriter<'_>,
    ) -> Result<bool> {
        let mut owner_inner = self.owner.inner.lock();
        let inner = self.inner.access_mut(&mut owner_inner);

        assert!(inner.delivery_state.has_pushed_node);
        if inner.delivery_state.has_pushed_wrapper {
            // If the wrapper is scheduled, then we are either a normal push or weak zero2one
            // increment, and the wrapper is a strong zero2one increment, so the wrapper always
            // takes precedence over us.
            assert!(inner.delivery_state.has_strong_zero2one);
            inner.delivery_state.has_pushed_node = false;
            inner.delivery_state.has_weak_zero2one = false;
            return Ok(true);
        }

        inner.delivery_state.has_pushed_node = false;
        inner.delivery_state.has_weak_zero2one = false;
        inner.delivery_state.has_strong_zero2one = false;

        self.do_work_locked(writer, owner_inner)
    }

    fn cancel(self: DArc<Self>) {}

    fn should_sync_wakeup(&self) -> bool {
        false
    }

    #[inline(never)]
    fn debug_print(&self, m: &SeqFile, prefix: &str, _tprefix: &str) -> Result<()> {
        seq_print!(
            m,
            "{}node work {}: u{:016x} c{:016x}\n",
            prefix,
            self.debug_id,
            self.ptr,
            self.cookie,
        );
        Ok(())
    }
}

#[pin_data(PinnedDrop)]
pub(crate) struct MultiplexedClaimWork {
    node: DArc<Node>,
    recipient: Arc<Process>,
    request_key: Atomic<u64>,
    request_id: Atomic<u64>,
    claim_id: u64,
    #[pin]
    terminal: SpinLock<Option<MultiplexedTerminal>>,
    #[pin]
    links_track: AtomicTracker,
    #[pin]
    node_links: ListLinks<1>,
    #[pin]
    node_links_track: AtomicTracker<1>,
    #[pin]
    recipient_links: ListLinks<2>,
    #[pin]
    recipient_links_track: AtomicTracker<2>,
}

impl MultiplexedClaimWork {
    fn try_new(node: DArc<Node>, recipient: Arc<Process>, claim_id: u64) -> Result<DArc<Self>> {
        DTRWrap::arc_pin_init(pin_init!(Self {
            node,
            recipient,
            request_key: Atomic::new(0),
            request_id: Atomic::new(0),
            claim_id,
            terminal <- kernel::new_spinlock!(None, "MultiplexedClaimWork::terminal"),
            links_track <- AtomicTracker::new(),
            node_links <- ListLinks::new(),
            node_links_track <- AtomicTracker::new(),
            recipient_links <- ListLinks::new(),
            recipient_links_track <- AtomicTracker::new(),
        }))
        .map(ListArc::into_arc)
    }

    fn set_claim(&self, key: u64, request_id: u64, terminal: MultiplexedTerminal) {
        self.request_key.store(key, Relaxed);
        self.request_id.store(request_id, Relaxed);
        *self.terminal.lock() = Some(terminal);
    }

    fn restore(&self, terminal: MultiplexedTerminal) {
        self.node
            .requeue_multiplexed_terminal(self.request_key.load(Relaxed), terminal);
        self.node.dispatch_multiplexed_claims();
    }

    pub(crate) fn cancel_pending(self: &DArc<Self>) {
        self.node.cancel_multiplexed_claim(self);
    }
}

impl DeliverToRead for MultiplexedClaimWork {
    fn required_read_size(&self) -> usize {
        mem::size_of::<u32>() + mem::size_of::<BinderMultiplexedReplyReceived>()
    }

    fn do_work(
        self: DArc<Self>,
        thread: &Thread,
        writer: &mut BinderReturnWriter<'_>,
    ) -> Result<bool> {
        let terminal = self.terminal.lock().take().ok_or(ESRCH)?;
        let reply_bytes = terminal.reply_bytes();
        let request_id = self.request_id.load(Relaxed);
        let ret = (|| -> Result {
            match &terminal {
                MultiplexedTerminal::Error { reason, error } => {
                    let status = BinderMultiplexedReplyError::new(
                        request_id,
                        self.claim_id,
                        *reason,
                        *error,
                    );
                    writer.write_code(BR_REPLY_MULTIPLEXED_ERROR)?;
                    writer.write_payload(&status)
                }
                MultiplexedTerminal::Reply(reply) => {
                    let mut info = TransactionInfo::zeroed();
                    info.from_pid = thread.process.task.pid();
                    info.data_size = reply.data.len();
                    info.flags = reply.flags;
                    let mut alloc = thread
                        .process
                        .buffer_alloc(super::next_debug_id(), reply.data.len(), &mut info)
                        .map_err(|err| err.source.unwrap_or(EINVAL))?
                        .success();
                    alloc.write(0, &reply.data[..])?;
                    if reply.flags & TF_CLEAR_BUF != 0 {
                        alloc.set_info_clear_on_drop();
                    }

                    let mut out = BinderMultiplexedReplyReceived::default();
                    let tr = out.tr_data();
                    tr.code = reply.code;
                    tr.flags = reply.flags;
                    tr.data_size = reply.data.len() as _;
                    tr.data.ptr.buffer = alloc.ptr as _;
                    tr.sender_euid = reply.sender_euid.into_uid_in_current_ns();
                    out.request_id = request_id;
                    out.claim_id = self.claim_id;
                    writer.write_code(BR_REPLY_MULTIPLEXED)?;
                    writer.write_payload(&out)?;
                    alloc.keep_alive();
                    Ok(())
                }
            }
        })();

        match ret {
            Ok(()) => {
                self.node
                    .complete_multiplexed_claim(self.request_key.load(Relaxed), reply_bytes);
                Ok(false)
            }
            Err(err) => {
                self.restore(terminal);
                Err(err)
            }
        }
    }

    fn cancel(self: DArc<Self>) {
        if let Some(terminal) = self.terminal.lock().take() {
            self.restore(terminal);
        }
    }

    fn should_sync_wakeup(&self) -> bool {
        true
    }

    fn debug_print(&self, m: &SeqFile, prefix: &str, _tprefix: &str) -> Result<()> {
        seq_print!(
            m,
            "{}multiplexed claim {}\n",
            prefix,
            self.request_id.load(Relaxed)
        );
        Ok(())
    }
}

#[pinned_drop]
impl PinnedDrop for MultiplexedClaimWork {
    fn drop(self: Pin<&mut Self>) {
        if let Some(terminal) = self.terminal.lock().take() {
            self.restore(terminal);
        }
    }
}

kernel::list::impl_list_arc_safe! {
    impl ListArcSafe<0> for MultiplexedClaimWork {
        tracked_by links_track: AtomicTracker;
    }
}

kernel::list::impl_list_item! {
    impl ListItem<0> for DTRWrap<MultiplexedClaimWork> {
        using ListLinks { self.links.inner };
    }
}

kernel::list::impl_list_arc_safe! {
    impl ListArcSafe<1> for MultiplexedClaimWork {
        tracked_by node_links_track: AtomicTracker<1>;
    }
    impl ListArcSafe<1> for DTRWrap<MultiplexedClaimWork> {
        tracked_by wrapped: MultiplexedClaimWork;
    }
    impl ListArcSafe<2> for MultiplexedClaimWork {
        tracked_by recipient_links_track: AtomicTracker<2>;
    }
    impl ListArcSafe<2> for DTRWrap<MultiplexedClaimWork> {
        tracked_by wrapped: MultiplexedClaimWork;
    }
}

kernel::list::impl_list_item! {
    impl ListItem<1> for DTRWrap<MultiplexedClaimWork> {
        using ListLinks { self.wrapped.node_links };
    }
    impl ListItem<2> for DTRWrap<MultiplexedClaimWork> {
        using ListLinks { self.wrapped.recipient_links };
    }
}

/// Represents something that holds one or more ref-counts to a `Node`.
///
/// Whenever process A holds a refcount to a node owned by a different process B, then process A
/// will store a `NodeRef` that refers to the `Node` in process B. When process A releases the
/// refcount, we destroy the NodeRef, which decrements the ref-count in process A.
///
/// This type is also used for some other cases. For example, a transaction allocation holds a
/// refcount on the target node, and this is implemented by storing a `NodeRef` in the allocation
/// so that the destructor of the allocation will drop a refcount of the `Node`.
pub(crate) struct NodeRef {
    pub(crate) node: DArc<Node>,
    /// How many times does this NodeRef hold a refcount on the Node?
    strong_node_count: usize,
    weak_node_count: usize,
    /// How many times does userspace hold a refcount on this NodeRef?
    strong_count: usize,
    weak_count: usize,
}

impl NodeRef {
    pub(crate) fn new(node: DArc<Node>, strong_count: usize, weak_count: usize) -> Self {
        Self {
            node,
            strong_node_count: strong_count,
            weak_node_count: weak_count,
            strong_count,
            weak_count,
        }
    }

    pub(crate) fn absorb(&mut self, mut other: Self) {
        assert!(
            Arc::ptr_eq(&self.node, &other.node),
            "absorb called with differing nodes"
        );
        self.strong_node_count += other.strong_node_count;
        self.weak_node_count += other.weak_node_count;
        self.strong_count += other.strong_count;
        self.weak_count += other.weak_count;
        other.strong_count = 0;
        other.weak_count = 0;
        other.strong_node_count = 0;
        other.weak_node_count = 0;

        if self.strong_node_count >= 2 || self.weak_node_count >= 2 {
            let mut guard = self.node.owner.inner.lock();
            let inner = self.node.inner.access_mut(&mut guard);

            if self.strong_node_count >= 2 {
                inner.strong.count -= self.strong_node_count - 1;
                self.strong_node_count = 1;
                assert_ne!(inner.strong.count, 0);
            }
            if self.weak_node_count >= 2 {
                inner.weak.count -= self.weak_node_count - 1;
                self.weak_node_count = 1;
                assert_ne!(inner.weak.count, 0);
            }
        }
    }

    pub(crate) fn get_count(&self) -> (usize, usize) {
        (self.strong_count, self.weak_count)
    }

    pub(crate) fn clone(&self, strong: bool) -> Result<NodeRef> {
        if strong && self.strong_count == 0 {
            return Err(EINVAL);
        }
        Ok(self
            .node
            .owner
            .inner
            .lock()
            .new_node_ref(self.node.clone(), strong, None))
    }

    /// Updates (increments or decrements) the number of references held against the node. If the
    /// count being updated transitions from 0 to 1 or from 1 to 0, the node is notified by having
    /// its `update_refcount` function called.
    ///
    /// Returns whether `self` should be removed (when both counts are zero).
    pub(crate) fn update(&mut self, inc: bool, strong: bool) -> bool {
        if strong && self.strong_count == 0 {
            return false;
        }
        let (count, node_count, other_count) = if strong {
            (
                &mut self.strong_count,
                &mut self.strong_node_count,
                self.weak_count,
            )
        } else {
            (
                &mut self.weak_count,
                &mut self.weak_node_count,
                self.strong_count,
            )
        };
        if inc {
            if *count == 0 {
                *node_count = 1;
                self.node.update_refcount(true, 1, strong);
            }
            *count += 1;
        } else {
            if *count == 0 {
                pr_warn!(
                    "pid {} performed invalid decrement on ref\n",
                    kernel::current!().pid()
                );
                return false;
            }
            *count -= 1;
            if *count == 0 {
                self.node.update_refcount(false, *node_count, strong);
                *node_count = 0;
                return other_count == 0;
            }
        }
        false
    }
}

impl Drop for NodeRef {
    // This destructor is called conditionally from `Allocation::drop`. That branch is often
    // mispredicted. Inlining this method call reduces the cost of those branch mispredictions.
    #[inline(always)]
    fn drop(&mut self) {
        if self.strong_node_count > 0 {
            self.node
                .update_refcount(false, self.strong_node_count, true);
        }
        if self.weak_node_count > 0 {
            self.node
                .update_refcount(false, self.weak_node_count, false);
        }
    }
}

struct NodeDeathInner {
    dead: bool,
    cleared: bool,
    notification_done: bool,
    /// Indicates whether the normal flow was interrupted by removing the handle. In this case, we
    /// need behave as if the death notification didn't exist (i.e., we don't deliver anything to
    /// the user.
    aborted: bool,
}

/// Used to deliver notifications when a process dies.
///
/// A process can request to be notified when a process dies using `BC_REQUEST_DEATH_NOTIFICATION`.
/// This will make the driver send a `BR_DEAD_BINDER` to userspace when the process dies (or
/// immediately if it is already dead). Userspace is supposed to respond with `BC_DEAD_BINDER_DONE`
/// once it has processed the notification.
///
/// Userspace can unregister from death notifications using the `BC_CLEAR_DEATH_NOTIFICATION`
/// command. In this case, the kernel will respond with `BR_CLEAR_DEATH_NOTIFICATION_DONE` once the
/// notification has been removed. Note that if the remote process dies before the kernel has
/// responded with `BR_CLEAR_DEATH_NOTIFICATION_DONE`, then the kernel will still send a
/// `BR_DEAD_BINDER`, which userspace must be able to process. In this case, the kernel will wait
/// for the `BC_DEAD_BINDER_DONE` command before it sends `BR_CLEAR_DEATH_NOTIFICATION_DONE`.
///
/// Note that even if the kernel sends a `BR_DEAD_BINDER`, this does not remove the death
/// notification. Userspace must still remove it manually using `BC_CLEAR_DEATH_NOTIFICATION`.
///
/// If a process uses `BC_RELEASE` to destroy its last refcount on a node that has an active death
/// registration, then the death registration is immediately deleted (we implement this using the
/// `aborted` field). However, userspace is not supposed to delete a `NodeRef` without first
/// deregistering death notifications, so this codepath is not executed under normal circumstances.
#[pin_data]
pub(crate) struct NodeDeath {
    node: DArc<Node>,
    process: Arc<Process>,
    pub(crate) cookie: u64,
    #[pin]
    links_track: AtomicTracker<0>,
    /// Used by the owner `Node` to store a list of registered death notifications.
    ///
    /// # Invariants
    ///
    /// Only ever used with the `death_list` list of `self.node`.
    #[pin]
    death_links: ListLinks<1>,
    /// Used by the process to keep track of the death notifications for which we have sent a
    /// `BR_DEAD_BINDER` but not yet received a `BC_DEAD_BINDER_DONE`.
    ///
    /// # Invariants
    ///
    /// Only ever used with the `delivered_deaths` list of `self.process`.
    #[pin]
    delivered_links: ListLinks<2>,
    #[pin]
    delivered_links_track: AtomicTracker<2>,
    #[pin]
    inner: SpinLock<NodeDeathInner>,
}

impl NodeDeath {
    /// Constructs a new node death notification object.
    pub(crate) fn new(
        node: DArc<Node>,
        process: Arc<Process>,
        cookie: u64,
    ) -> impl PinInit<DTRWrap<Self>> {
        DTRWrap::new(pin_init!(
            Self {
                node,
                process,
                cookie,
                links_track <- AtomicTracker::new(),
                death_links <- ListLinks::new(),
                delivered_links <- ListLinks::new(),
                delivered_links_track <- AtomicTracker::new(),
                inner <- kernel::new_spinlock!(NodeDeathInner {
                    dead: false,
                    cleared: false,
                    notification_done: false,
                    aborted: false,
                }, "NodeDeath::inner"),
            }
        ))
    }

    /// Sets the cleared flag to `true`.
    ///
    /// It removes `self` from the node's death notification list if needed.
    ///
    /// Returns whether it needs to be queued.
    pub(crate) fn set_cleared(self: &DArc<Self>, abort: bool) -> bool {
        let (needs_removal, needs_queueing) = {
            // Update state and determine if we need to queue a work item. We only need to do it
            // when the node is not dead or if the user already completed the death notification.
            let mut inner = self.inner.lock();
            if abort {
                inner.aborted = true;
            }
            if inner.cleared {
                // Already cleared.
                return false;
            }
            inner.cleared = true;
            (!inner.dead, !inner.dead || inner.notification_done)
        };

        // Remove death notification from node.
        if needs_removal {
            let mut owner_inner = self.node.owner.inner.lock();
            let node_inner = self.node.inner.access_mut(&mut owner_inner);
            // SAFETY: A `NodeDeath` is never inserted into the death list of any node other than
            // its owner, so it is either in this death list or in no death list.
            unsafe { node_inner.death_list.remove(self) };
        }
        needs_queueing
    }

    /// Sets the 'notification done' flag to `true`.
    pub(crate) fn set_notification_done(self: DArc<Self>, thread: &Thread) {
        let needs_queueing = {
            let mut inner = self.inner.lock();
            inner.notification_done = true;
            inner.cleared
        };
        if needs_queueing {
            if let Some(death) = ListArc::try_from_arc_or_drop(self) {
                let _ = thread.push_work_if_looper(death);
            }
        }
    }

    /// Sets the 'dead' flag to `true` and queues work item if needed.
    pub(crate) fn set_dead(self: DArc<Self>) {
        let needs_queueing = {
            let mut inner = self.inner.lock();
            if inner.cleared {
                false
            } else {
                inner.dead = true;
                true
            }
        };
        if needs_queueing {
            // Push the death notification to the target process. There is nothing else to do if
            // it's already dead.
            if let Some(death) = ListArc::try_from_arc_or_drop(self) {
                let process = death.process.clone();
                let _ = process.push_work(death);
            }
        }
    }
}

kernel::list::impl_list_arc_safe! {
    impl ListArcSafe<0> for NodeDeath {
        tracked_by links_track: AtomicTracker;
    }
}

kernel::list::impl_list_arc_safe! {
    impl ListArcSafe<1> for DTRWrap<NodeDeath> { untracked; }
}
kernel::list::impl_list_item! {
    impl ListItem<1> for DTRWrap<NodeDeath> {
        using ListLinks { self.wrapped.death_links };
    }
}

kernel::list::impl_list_arc_safe! {
    impl ListArcSafe<2> for DTRWrap<NodeDeath> {
        tracked_by wrapped: NodeDeath;
    }
}
kernel::list::impl_list_arc_safe! {
    impl ListArcSafe<2> for NodeDeath {
        tracked_by delivered_links_track: AtomicTracker<2>;
    }
}
kernel::list::impl_list_item! {
    impl ListItem<2> for DTRWrap<NodeDeath> {
        using ListLinks { self.wrapped.delivered_links };
    }
}

impl DeliverToRead for NodeDeath {
    fn do_work(
        self: DArc<Self>,
        _thread: &Thread,
        writer: &mut BinderReturnWriter<'_>,
    ) -> Result<bool> {
        let done = {
            let inner = self.inner.lock();
            if inner.aborted {
                return Ok(true);
            }
            inner.cleared && (!inner.dead || inner.notification_done)
        };

        let cookie = self.cookie;
        let cmd = if done {
            BR_CLEAR_DEATH_NOTIFICATION_DONE
        } else {
            let process = self.process.clone();
            let mut process_inner = process.inner.lock();
            let inner = self.inner.lock();
            if inner.aborted {
                return Ok(true);
            }
            // We're still holding the inner lock, so it cannot be aborted while we insert it into
            // the delivered list.
            process_inner.death_delivered(self.clone());
            BR_DEAD_BINDER
        };

        writer.write_code(cmd)?;
        writer.write_payload(&cookie)?;
        // DEAD_BINDER notifications can cause transactions, so stop processing work items when we
        // get to a death notification.
        Ok(cmd != BR_DEAD_BINDER)
    }

    fn cancel(self: DArc<Self>) {}

    fn should_sync_wakeup(&self) -> bool {
        false
    }

    #[inline(never)]
    fn debug_print(&self, m: &SeqFile, prefix: &str, _tprefix: &str) -> Result<()> {
        let inner = self.inner.lock();

        let dead_binder = inner.dead && !inner.notification_done;

        if dead_binder {
            if inner.cleared {
                seq_print!(m, "{}has cleared dead binder\n", prefix);
            } else {
                seq_print!(m, "{}has dead binder\n", prefix);
            }
        } else {
            seq_print!(m, "{}has cleared death notification\n", prefix);
        }

        Ok(())
    }
}
