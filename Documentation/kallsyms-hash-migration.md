# Kallsyms hash-first plan (fresh start)

Goal: stop caring about enormous mangled symbol strings in the kernel by treating hashes as the real
identity and reserving printable names for user-facing output. Rust mangled names become a
non-issue; C modules can benefit too. Do this with kernel-standard migration mechanics (additive
APIs, optional strict mode, incremental conversions).

## Representations and when to use them

- **Hash identity (primary)**: 64-bit stable hash + type + length, always emitted for vmlinux and
  modules. Used for resolution, matching, and linking. Kernel-internal lookups should prefer this
  path.
- **Printable name (secondary)**: demangled/pretty string for human-facing output only. The kernel
  should not need the mangled form except for optional diagnostics.
- **How to pick**:
  - If the caller needs to _match/resolve_ a symbol (e.g., module linking, kprobes blacklist, BPF/ftrace/kallsyms lookups), use the hash identity and type/len. No string needed.
  - If the caller needs to _emit text to userspace_ or logs (e.g., stack traces, /proc/kallsyms,
    perf, trace printing), request the printable string. Use bounded expansion helpers that accept
    caller-provided buffers.
  - For ambiguous cases, default to hash unless the output is consumed by humans or stable user ABI text.

## Kernel implementation sketch

- Build artifacts:
  - `kallsyms_hashes`, `kallsyms_uncompressed_lens`, and `kallsyms_sym_types` emitted for vmlinux and modules.
  - Printable (demangled where applicable) strings kept for legacy interfaces; mangled strings kept only if explicitly requested (debug knob).
- APIs (additive, type-separated):
  - Identity: `struct ksym_id { u64 hash; u32 len; u8 type; }` plus helpers (`kallsyms_get_id()`, `kallsyms_lookup_id()`), and module/BPF/ftrace equivalents. Resolution/matching paths take `struct ksym_id`.
  - Display: `kallsyms_get_printable()` (bounded expansion into caller buffer) for user-facing output. Keep `%pS`, `/proc/kallsyms`, perf, trace printing on this path.
  - Legacy string lookups remain temporarily but become unattractive under strict mode (see below); a thin inline can forward to the new helpers for compatibility.
- Stack traces and printk `%pS`:
  - Keep using printable names (demangled where available). Internally, lookup can be hash-first, then expand only the chosen symbol for display.
- /proc/kallsyms and perf:
  - Continue to serve printable names; add hashed sections so tools can consume hashes for matching if desired.
- Rust/C modules:
  - Link by hash identity; printable names supplied separately for diagnostics.

## Migration mechanics (kernel-style)

- Additive API + opt-in strict mode:
  - Introduce the new identity/display APIs and types.
  - Add `CONFIG_KALLSYMS_STRICT_ID` (under DEBUG/EXPERT, default n) that hides legacy prototypes and turns legacy use into build errors. Enable this in CI/-next to force compiler-driven coverage without burdening regular builds.
  - For normal builds, keep legacy wrappers but add compiler diagnostics (e.g., `#pragma GCC diagnostic warning` around the prototypes) so `W=1` surfaces stragglers.
  - Remove `KSYM_NAME_LEN`/`KSYM_SYMBOL_LEN` entirely: lengths come from the tables or from caller-provided buffers. This must be complete before posting to LKML so downstream users cannot continue depending on the legacy constants.
  - Stop double-storing length/type: move string expansion to use the dedicated length/type tables, then remove length/type/terminator dependence from the compressed blob once consumers are switched.
- Type separation:
  - Identity consumers take `struct ksym_id`, not `const char *`. Display consumers take buffers/len for printable names. This makes misuse a type error when strict mode is on.
- Rollout steps:
  1) Land identity structs/APIs and display helper; convert kallsyms core/module loader/stacktrace to use them.
  2) Turn on `CONFIG_KALLSYMS_STRICT_ID` in CI/-next to surface remaining legacy callers; fix in batches.
  3) Once clean, consider gating legacy wrappers behind EXPERT or removing them.
- Userspace stability:
  - Printable interfaces stay unchanged; hashes are additive for tools that want them.

## Patch series sketch (staged across cycles)

Series A (introduce without disruption):
1. Add `struct ksym_id` and identity helpers; add display helper.
2. Keep legacy APIs as thin wrappers with `W=1` warnings.
3. Add `CONFIG_KALLSYMS_STRICT_ID` (default off) and wire diagnostics.
4. Convert core kallsyms lookup/module loader/stacktrace to new APIs.

Series B (early conversions + tooling):
5. Convert kprobes blacklist and related kallsyms users to `ksym_id` (identity) and printable for output.
6. Convert ftrace/BPF symbol lookups to use identity helpers; keep printing on display path.
7. Convert lockdep key names to identity lookups; printable for reporting.
8. Expose hashed sections to perf/tools while retaining printable fallback.

Series C (enforcement and cleanup in -next/CI):
9. Enable `CONFIG_KALLSYMS_STRICT_ID=y` in -next/CI configs; fix resulting build errors in batches.
10. Delete `KSYM_NAME_LEN`/`KSYM_SYMBOL_LEN` and any buffer assumptions; push explicit lengths or table-derived lengths through all call sites so the constants disappear.
11. Gate legacy wrappers behind EXPERT or drop them once the tree is clean under strict mode.
12. Remove temporary diagnostics once no users remain.

## Workflow (with b4)

- The human invokes `b4 prep -n ...` to create the work branch; commits are made with `git commit -s`.
- Checks: run `b4 prep --check` (and the build notes above).
- Cover letter: draft text can be supplied in a file for manual paste; the interactive `b4 prep --edit-cover` remains a human step.

## Build note

Quick build sanity check:

```
source bee-init
tools/testing/kunit/kunit.py build --arch arm64 --make_options LLVM=1 --make_options W=1 --kconfig_add CONFIG_BPF_SYSCALL=y --kconfig_add CONFIG_BPF_JIT=y
```

Faster incremental:

```
source bee-init
make W=1 LLVM=1 ARCH=arm64 O=.kunit -j$(nproc) all
```
