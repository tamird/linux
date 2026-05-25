.. SPDX-License-Identifier: GPL-2.0

=======================================
Binder multiplexed transaction protocol
=======================================

Binder normally represents a synchronous two-way transaction by associating
the request with the calling Binder thread until the reply is returned.
Multiplexed transactions provide an alternative two-way protocol in which the
caller supplies a request identifier and a Binder node retains terminal
results until they can be delivered through a claim posted by one of its
handle holders.  Replies can complete in any order and be demultiplexed by
userspace.

Multiplexed transactions use commands and returns in the data streams passed
through ``BINDER_WRITE_READ``.  They carry a normal
``struct binder_transaction_data`` payload in addition to the fields
documented below.  There are no multiplexed counterparts to
``BC_TRANSACTION_SG``; explicitly multiplexed requests and their terminal
replies cannot carry payloads which require
``struct binder_transaction_data_sg``.  An ordinary caller delivered through
the multiplexed server interface can receive a token reply using
``BC_REPLY_MULTIPLEXED_SG``.

Design goals and constraints
============================

The protocol is intended to let a service receive multiple in-flight two-way
calls on one Binder node and complete them independently of the thread which
received each request or the order in which they arrived.  Userspace owns the
dispatch and demultiplexing policy: for explicitly multiplexed calls, an
authorized holder of a transferred node handle may claim terminal results.

Multiplexed delivery is a property of the service node.  This lets a service
adopt token-based dispatch while continuing to serve unchanged ordinary
two-way callers, and gives it a single node-retirement operation which stops
new work and releases retained protocol state.

The protocol deliberately does not infer ownership from a particular thread
or process, or protect against userspace sharing a node handle among endpoints
which should not share completions.  Services requiring that isolation must
publish separate nodes.

Compatibility is asymmetric.  Ordinary two-way calls can be delivered through
the token interface to a service which has opted in.  Explicitly multiplexed
calls are not delivered to an ordinary service: doing so would retain
claimable state for a server which did not opt in, and an ordinary reply may
contain Binder objects, file descriptors, or scatter-gather data which cannot
be translated until a claimant is known.  For the same reason, explicitly
multiplexed terminal replies are limited to raw payload data.

Ordinary two-way calls delivered through the token interface also do not
preserve synchronous nested-call routing back to the caller's blocked Binder
thread.  A service which depends on that behavior must not enable multiplexed
delivery on that node.

Availability and opt-in
=======================

Applications can detect support for this protocol on a binderfs mount by
testing for a ``features/multiplexed_transactions`` file containing ``1``.

An owner that participates in this protocol publishes its node with
``FLAT_BINDER_FLAG_MULTIPLEXED_DELIVERY``.  An explicit multiplexed request
to a node without this flag is rejected and is not delivered.

Two-way ordinary transactions sent to a node with multiplexed delivery are
delivered to its owner as multiplexed requests with
``BINDER_MULTIPLEXED_DELIVERY_ORDINARY`` set in ``delivery_flags``.  When the
owner replies through the returned token, the caller receives an ordinary
``BR_REPLY``.  A server can therefore adopt multiplexed dispatch without
requiring its existing callers to use a new protocol.  Ordinary one-way
transactions continue to use ordinary Binder delivery while the node is
active.  This compatibility does not preserve legacy nested-call routing back
to the ordinary caller's blocked thread; services that rely on synchronous
callbacks to that thread must continue to use ordinary delivery.

Multiplexed transaction state is associated with the target Binder node.
Subject to the Binder transaction security check described below, any process
holding a strong handle to a multiplexed-delivery node can post
reply claims for its queued terminal results.  A service requiring per-client
completion isolation should therefore publish distinct private nodes rather
than enable this protocol on a node shared by unrelated clients.  Subject to
that security check, transferring a node handle transfers the ability to
receive its terminal results.

Request lifecycle
=================

A client submits a request using ``BC_TRANSACTION_MULTIPLEXED`` and
``struct binder_multiplexed_transaction``.  The ``request_id`` is selected by
userspace and may be zero.  It is an opaque tag copied into the terminal
return; the driver does not require it to be unique:

* ``BR_REPLY_MULTIPLEXED`` returns a successful reply with the same
  ``request_id``.
* ``BR_REPLY_MULTIPLEXED_ERROR`` returns a terminal failure with the same
  ``request_id``.

``TF_ONE_WAY`` and ``TF_UPDATE_TXN`` are invalid for
``BC_TRANSACTION_MULTIPLEXED``.  Multiplexed requests do not participate in
Binder's synchronous transaction stack, and submission does not generate a
``BR_TRANSACTION_COMPLETE`` return.  Once accepted, a request remains
associated with the target node until one terminal result is delivered through
a posted claim or the node is retired.

Invalid request flags, an unsupported target node, or failure to reserve
node-side state reject the command through ``BINDER_WRITE_READ``; in these
cases the driver has not accepted a request and does not create a terminal
result.

Although a multiplexed request does not use the synchronous transaction
stack, it remains a two-way request for Binder freeze handling.  Pending
requests and outstanding reply tokens count as pending transaction state.  A
frozen destination can therefore terminate a multiplexed request with
``BINDER_MULTIPLEXED_REPLY_FROZEN``.  There is no per-request command for
canceling an accepted multiplexed request or an issued reply token.

Multiplexed transaction state belongs to the target node, rather than to the
process which submitted a request.  Transferring a reference to that node does
not cancel requests or replies.  A strong handle is required to post a reply
claim, and posting it remains subject to the Binder transaction security
check.

Pending multiplexed transaction state keeps the target node resident even if
all ordinary references to it are released; in particular, releasing a
received request buffer does not invalidate its reply token.  The service can
retire a multiplexed node it owns by submitting
``BC_RETIRE_MULTIPLEXED_NODE`` with that local node's pointer and
cookie.  Posted claims which can be paired at retirement receive their terminal
results; incomplete requests complete with
``BINDER_MULTIPLEXED_REPLY_SHUTDOWN`` before this pairing.  Other state is
abandoned and outstanding reply tokens are invalidated.  On a node published
with multiplexed delivery, no new transaction or reply claim may be posted;
an ordinary caller with an outstanding token receives ``BR_DEAD_REPLY``.
Closing the endpoint owning a node also retires it; incomplete multiplexed
requests report ``BINDER_MULTIPLEXED_REPLY_DEAD`` in that case.
Retirement does not retract a request already copied into a concurrent
``BINDER_WRITE_READ`` read; any token returned by such a read has already
been invalidated and cannot be used to submit a reply.

``BC_RETIRE_MULTIPLEXED_NODE`` is accepted only for a node published with
``FLAT_BINDER_FLAG_MULTIPLEXED_DELIVERY``.

Receiving and replying
======================

A server receives a multiplexed request as
``BR_TRANSACTION_MULTIPLEXED`` or
``BR_TRANSACTION_MULTIPLEXED_SEC_CTX``.  The returned
``struct binder_multiplexed_transaction_received`` contains:

``request_id``
  The caller-selected identifier for ``BC_TRANSACTION_MULTIPLEXED`` requests.
  The value is zero for a request sent through ordinary ``BC_TRANSACTION``;
  use ``delivery_flags`` rather than this value to identify that case because
  an explicitly multiplexed caller may also select zero.

``reply_token``
  An opaque, single-use capability used with ``BC_REPLY_MULTIPLEXED``.  The
  token is scoped to the receiving Binder process endpoint.  Any Binder
  thread using that endpoint can submit the reply, allowing processing to be
  dispatched independently of the thread which received the request.

``delivery_flags``
  ``BINDER_MULTIPLEXED_DELIVERY_ORDINARY`` indicates that the caller submitted
  an ordinary two-way transaction and will receive an ordinary reply.

The server may release the received transaction buffer with
``BC_FREE_BUFFER`` before replying; this does not invalidate the
``reply_token``.  Servers reply using ``BC_REPLY_MULTIPLEXED`` and
``struct binder_multiplexed_reply``.  For a request with
``BINDER_MULTIPLEXED_DELIVERY_ORDINARY``, a server may instead use
``BC_REPLY_MULTIPLEXED_SG`` and ``struct binder_multiplexed_reply_sg``.
Replies for different requests may be submitted in any order.

``TF_ONE_WAY`` and ``TF_UPDATE_TXN`` are invalid for multiplexed reply
commands.  Before accepting a reply, the driver validates its token.  Invalid
flags or a zero, invalid, or consumed token reject the reply command.  A reply
to an explicit multiplexed request becomes a terminal result queued on the
target node; a reply to an ordinary request completes its ordinary caller.

For an explicitly multiplexed request, the receiving process is not known when
the server submits a reply.  Such a ``BC_REPLY_MULTIPLEXED`` requires
``offsets_size`` to be zero; it may carry raw bytes but not Binder objects or
file descriptors.  Translation of such objects would have to be performed
only after a claimant is selected.  A token reply to an ordinary request is
translated directly for its known caller and may use ordinary Binder object
and scatter-gather translation.  The driver limits retained successful reply
payloads for each node-owning Binder endpoint to 4 MiB.

Claiming replies
================

A process which holds a strong handle to a multiplexed-delivery node posts a
reply claim by submitting
``BC_CLAIM_MULTIPLEXED_REPLY`` with
``struct binder_multiplexed_reply_claim``.  ``claim_id`` is an opaque
userspace identifier echoed in the terminal return so one endpoint may post
claims for more than one node.  ``reserved`` must be zero.  The node must
have an outstanding request without an existing posted claim; excess claims
are rejected.

Claim submission is subject to the Binder transaction security check from the
node-owning endpoint to the claiming endpoint.

The driver pairs claims in submission order with completed terminal results in
completion order.  Delivery work for paired terminal results is placed on the
claiming Binder endpoint's process work queue; it is not tied to the thread
which posted the claim, and may be received by any of that endpoint's looper
threads.  The endpoint must service process work as a Binder looper to receive
it.  If no terminal result is ready, the claim remains posted; the claiming
Binder endpoint becomes readable after a matching result is ready:

* a successful result is returned as ``BR_REPLY_MULTIPLEXED``;
* a failed result is returned as ``BR_REPLY_MULTIPLEXED_ERROR``.

Before the node is retired, if delivery of a paired terminal result is
canceled before reaching userspace, the result is placed back on the node for
a later posted claim.  A paired result whose delivery is canceled after
retirement is discarded because no new claim may be posted.  A process may
submit a request, transfer or release the node
handle after another process has acquired it, and allow that recipient to
receive the terminal result if permitted by the Binder transaction security
check.
If an endpoint closes with unpaired reply claims posted, those claims are
withdrawn without canceling the associated requests.

Terminal request errors
=======================

``BR_REPLY_MULTIPLEXED_ERROR`` contains a terminal failure reason and an
optional negative errno in ``error``:

``BINDER_MULTIPLEXED_REPLY_DEAD``
  The destination became unavailable before it could return a reply.

``BINDER_MULTIPLEXED_REPLY_SHUTDOWN``
  The owner retired the target node before a reply was returned.

``BINDER_MULTIPLEXED_REPLY_FAILED``
  The accepted request or reply could not otherwise be delivered.

``BINDER_MULTIPLEXED_REPLY_FROZEN``
  The request failed because the destination was frozen.

``BINDER_MULTIPLEXED_REPLY_RESOURCE_EXHAUSTED``
  The destination could not reserve state needed to return a reply.

For terminal-error returns, ``error`` is zero when no more specific error
applies and otherwise contains a negative errno value.

Example flow
============

A server capable of processing requests concurrently can use this protocol as
follows:

1. Publish its Binder node with ``FLAT_BINDER_FLAG_MULTIPLEXED_DELIVERY``.
2. Receive requests through ``BR_TRANSACTION_MULTIPLEXED`` and retain each
   ``reply_token`` while dispatching the work.
3. Reply as each operation finishes using ``BC_REPLY_MULTIPLEXED`` and its
   corresponding token, without preserving receive order.

A client can submit several ``BC_TRANSACTION_MULTIPLEXED`` requests, post
reply claims, and associate each
``BR_REPLY_MULTIPLEXED`` or ``BR_REPLY_MULTIPLEXED_ERROR`` with its pending
operation by ``request_id`` and ``claim_id``.  It may instead transfer the
node handle to another process, which can post those reply claims if permitted
by the Binder transaction security check.

An unchanged client may instead submit ordinary two-way transactions to the
same node.  The server receives those transactions with reply tokens and the
client receives ordinary replies, provided that the operation does not rely
on legacy nested-call routing back to the blocked caller thread.
