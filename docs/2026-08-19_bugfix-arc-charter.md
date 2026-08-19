# The bug-fix arc charter — BUG-058, BUG-057, BUG-056 (2026-08-19, DRAFT for user review)

The three machine bugs the spec-truth campaign found (P3, all
audit-hardened diagnoses in `docs/BUGS.md`), fixed in one arc, ordered
by blast-radius-to-raft. All three are **silent-wrong-answer class** —
exactly what the doctrine says a green gate cannot see — and all three
already have red pinned guardrail cases, so every fix is a
red-to-green flip against pre-existing pins, never a case written to
match an implementation.

**Why this arc precedes W4 stage-2 (the tracker differential):** raft
code leans constantly on `if v, ok := m[k]; ok && f(v)` (BUG-058's
trigger shape — the P3 audit noted the original mis-diagnosis would
have "permanently darkened" it) and on two-var comma-ok declarations
(BUG-057). Tracker differentials run before these fixes could carry
masked greens or spurious reds; after them, W4's signal is clean.
This lane owns `Corpus/` + `baselines/` for its duration.

## Slice 1 — BUG-058: the if-init condition-hoist scope (frontend)

The diagnosed defect: `emitIf` (tools/nativefrontend/emit.go:2426)
emits `st.Init` inside the if node but the condition under the
ENCLOSING hoist accumulator, so hoisted condition work lands before
the init — wrong order (modes 2–3, silent) or stuck (mode 1). Fix
direction per the entry: scope the condition's hoist accumulator
inside the emitted if, emitIf-local.

1. **Edge enumeration FIRST** (guardrails-first; red or
   confirmed-green before the fix): `else if` chains (each condition's
   accumulator), if-with-init inside function literals, nested
   if-inits, init-panics-before-cond-hoist vs cond-panics-after-init,
   the comma-ok + short-circuit raft shape
   (`if v, ok := m[k]; ok && f(v)`) as an integration case, and
   re-probes of the structurally-corroborated non-affected relatives
   (for-init, switch-init, type-switch-init) as pinned greens so the
   fix cannot regress them silently.
2. The fix. All three existing pins (`if-init-hoist-order/*`,
   `panic-values/panic-error`) plus the new reds flip in one commit
   with the re-pin and reason; nothing else moves.
3. **Masked-green sweep**: modes 2–3 yield wrong answers that can
   coincide with right ones. Sweep the spec-examples dispositions and
   the exec corpus for if-with-init cases currently green whose
   green is not load-bearing (the BUG-056/057 masked-green pattern);
   add unmasking rows where the disposition's reasoning depended on
   order.

## Slice 2 — BUG-057: the two-var comma-ok var-decl arity hole (frontend)

The diagnosed defect: emit.go:2383-2392 pairs decl names to init
values with no arity check; function-local `var v, ok = <-ch` /
`= m[k]` / (probe: `= x.(T)`) delivers the value and drops `ok`.
Package-level is correct via `$pkginit`.

1. Edge enumeration first: all three comma-ok sources (receive, map
   index, type assertion) × typed/untyped × blank `_` in either
   position × function-local/package-level; plus the adjacent
   `var a, b = two()` tuple decl, which today FAILS CLOSED — pin
   that behavior explicitly so the fix cannot silently flip it to a
   new mis-lower.
2. The fix: an arity check at the pairing site, comma-ok var decls
   lowered through the same path as the (correct) short-decl form.
   If the clean mechanism naturally also supports the tuple-call
   decl, that is a judgment call to take or defer — logged either
   way; supporting it half-way is forbidden (fail closed or full).
3. The four pins + new reds flip same-commit with the re-pin.

## Slice 3 — BUG-056: `&*p` nil collapse (DESIGN-GATED)

The subtle one. The wire for `&*p` and `&(*p)` is byte-identical —
both collapse to `q := p` — so the nil-indirection panic the spec
demands (spec#Address_operators) never fires. The fix is NOT
obviously frontend-local:

1. **Probe matrix + design memo first, no implementation**: shapes
   `&*p`, `&(*p)`, `&**pp`, `&*p` under field/index composition, and
   corpus witnesses for `&p.f`/`&p[i]` on nil (currently record-only
   in the BUG entry). Then the mechanism options, argued in a dated
   memo: (a) frontend desugar to an explicit nil-check-then-address —
   but a naive `_ = *p` prefix materializes a LOAD gc never performs,
   a granularity-ledger violation (unobservable sequentially, real
   under concurrency — BUG-002's class); (b) a GoCore nil-assert /
   addr-of-indirection node — a semantic-core change; (c) anything
   better the probes suggest. The memo consults the granularity
   ledger (`docs/2026-07-23_reshape-r1r2-machine-design.md` §1) and
   the latitude inventory, and states each option's step-decomposition
   footprint.
2. **USER GATE — hard pause.** Any route that touches GoCore or adds
   a step/load absent from gc's observable behavior requires Mike's
   sign-off on the memo before a line of implementation. Per the
   long-cycle conventions, pausing here is the expected path, not a
   failure; slices 1–2 land regardless.
3. On the ruling: implement, flip the two pinned reds
   (`addr-deref-nil`, `addr-deref-nil-paren`), re-pin same-commit.

## Slice 4 — BUG-005: live map iteration (DESIGN-GATED; added at user
direction 2026-08-19 — "the deliberately pinned bugs should be fixed")

The oldest open red (2026-07-26): map `range` snapshots entries at
iteration start, so it observes neither delete/clear nor value
updates (spec is explicit: deleted entries "will not be produced"),
and — the S3 audit's fourth symptom — performs no per-iteration user-
memory read, making concurrent map writes invisible to the race
detector. Three differential reds + `race/negative/map-range-iter`.

1. **Design memo first, no implementation**: the live-read iteration
   model (gc reads at every `mapIterNext`) vs the snapshot model;
   what a per-iteration read step does to the granularity ledger
   (this is BUG-002's class — the decision IS the design); the
   added-entries envelope (spec: new entries "may be produced ... or
   may be skipped" — a genuine latitude point INSIDE the fix, so the
   memo must state the envelope, not pick gc's member silently);
   race-detector integration (the per-iteration read the S3 detector
   must see); interaction with the mirror evaluator's Q3 quit (the
   Sym mapIterK arm quits — confirm the fix does not widen the
   mirror's obligations).
2. **USER GATE — hard pause** on the memo: this is an interpreter/
   GoCore change, always gated. Slices 1–2 land regardless.
3. On the ruling: implement, flip the three map reds (the race
   negative flips when the detector sees the read), re-pin
   same-commit, and record the added-entries choice in the latitude
   inventory with its membership/re-envelope obligation.

## The arc's end-state claim (the honest ledger)

After this arc, the differential-red set is EXACTLY the pins that
must not be "fixed" by matching gc: BUG-061's staticinit residual +
`init/hidden-dep-order` (optimizer-dependent init-order latitude,
L-011 — gc's own answer changes under `-N -l`) and BUG-059
(non-injective panic rendering). Each carries its ledger entry and
its W3.2 re-envelope obligation; zero unexplained reds. Forcing
those three green against one compiler's optimizer would be modeling
gc, not Go — the doctrine's exact anti-goal.

## Cross-cutting obligations

- **Untriaged-25 cross-check** (end of arc): re-run the P3 untriaged
  spec-example dispositions against the fixed machine; any that these
  three fixes explain get their disposition updated with the BUG
  cross-reference — found-by-fix is corpus signal, not coincidence.
- **Validation gate per slice**: full `scripts/ci --diff` (runtime
  code changes every slice); flips exactly the predicted set;
  baseline re-pinned in the fix commit with the reason. No oracle
  weakening, no case edits to make anything pass.
- **BUGS.md**: each entry moves open → fixed with the fix commit,
  mechanism one-liner, and the flip list, same-commit.

## DONE (a conjunction)

1. BUG-058 fixed; all its pins green; edge set + raft-shape
   integration case landed; non-affected relatives pinned green;
   masked-green sweep recorded (rows added or "none found" with the
   sweep's scope stated).
2. BUG-057 fixed; all four pins + edge set green; the tuple-decl
   fail-closed behavior explicitly pinned; the take-or-defer call
   logged.
3. BUG-056: probe matrix + design memo delivered and EITHER the
   user-ruled mechanism implemented with both pins green OR the gate
   outcome recorded (deferral is a legitimate end-state if Mike rules
   the mechanism needs the re-envelope arc's machinery — the arc is
   then DONE with 056 documented as gated, never half-implemented).
4. BUG-005: same structure as 056 — memo + gate outcome, implemented
   or explicitly deferred, never half. If implemented: three map reds
   + the race negative green, the added-entries latitude recorded.
5. The end-state claim verified: the differential-red set is exactly
   the named latitude/rendering pins, cross-referenced to ledger +
   W3.2.
6. Untriaged-25 cross-check recorded.
7. `scripts/ci --diff` green at tip; every flip predicted; BUGS.md
   current; arc log (`docs/bugfix-arc-log.md`) current.
8. Pre-merge audit ASK posed (proposed size: 1 Opus reviewer for
   the frontend slices + 1 Fable reviewer for the semantic-core
   slice if BUG-005 is implemented — the interpreter is the primary
   dimension, always audited; Mike may trim/waive).

## Boundaries (hard)

- No GoCore/semantic-core change without the slice-3/slice-4 gates —
  those are the arc's designed pauses.
- This lane owns `Corpus/` + `baselines/`; W4 stage-2 does not start
  until this arc lands (worktree discipline).
- Fix commits touch the frontend + corpus + baselines + BUGS.md +
  log; anything else is scope drift and gets logged before it gets
  done.
- Workers: slices 1–2 are Opus-executable (diagnosed mechanisms,
  mechanical-adjacent); the slice-3 and slice-4 memos and any gated
  implementation are Fable (conceptual, granularity reasoning). Judgment calls logged in the arc log for
  user review, per the standing conventions.
