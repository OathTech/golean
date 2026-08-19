# The bug-fix + frontier arc charter (2026-08-19, DRAFT for user review)

Scope set by user direction 2026-08-19: fix BUG-058/057/056/005; then
**all bugs and differentials are killed unless there is a profound
reason they exist** (each such reason written down and put to the
user); and the arc **stakes out the unsupported frontier** — a
guardrail suite strong enough that future feature arcs start with
their targets pinned.

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

## Slice 5 — the full red/bug triage (kill or justify, nothing else)

The complete accounting, mechanized as a tracked triage table
(`docs/bugfix-arc-log.md` §triage): **all 13 open BUGS.md entries**
and **all 136 baseline reds** (12 differential, 87 frontend-export,
35 lean-observation, 1 go-run, 1 nondet — the counts at charter time;
re-derive at execution). Every row lands in exactly one category:

- **(a) FIXED in this arc** — pulled into slices 1–4, or a new
  mini-slice when the fix is cheap and diagnosed (judgment call,
  logged). The receive-hoist family (BUG-023/026) is expected
  category-(a) candidates — same evaluation-order class as BUG-058;
  triage confirms.
- **(b) FRONTIER** — red because the feature is unsupported; the row
  names the feature and hands it to slice 6. Expected home of most
  of the 87 frontend-export reds.
- **(c) PROFOUND-REASON PIN** — latitude (optimizer-dependent,
  spec-open) or impossibility (non-injective rendering); the row
  carries the ledger entry and the re-envelope obligation. The known
  three (BUG-061 residual, hidden-dep-order, BUG-059) start here;
  anything else claiming (c) must argue it fresh.

There is NO fourth category. "Known issue" without a written profound
reason is not a state this arc may end in. The category-(c) list is
put to the user at the arc gate — profound-ness is the user's call,
not ours.

## Slice 6 — the unsupported frontier, staked out

For every feature the frontend refuses (the refusal census from the
frontier sweep + slice 5's category-(b) rows): build the guardrail
suite BEFORE any support exists, per the doctrine ("a tool feature is
not started until its guardrail cases exist and classify correctly").

1. **The frontier map** (`docs/frontier-map.md`, tracked): feature →
   refusal point (file:line, the error string) → oracle-verified
   guardrail case ids → the spec anchors → estimated implementation
   scope (frontend-only / GoCore-touching / envelope-question). This
   is the coverage roadmap the arc leaves behind.
2. **The suite**: per feature, isolated cases + edge enumeration
   (three-layer strategy, `docs/native-frontend-goal.md`), expected
   outputs computed from `go run` and hand-argued against the spec.
   Every case must classify as a visible frontend/feature-blocked
   red — never a false pass, never silently skipped. These land in
   the baseline as explained frontend-export rows: the frontier
   becomes ENUMERATED red, not absent grey.
3. Depth is a judgment call per feature, logged: a feature near the
   raft path (goroutines/channels/select/sync, interfaces, defer
   breadth) gets the full enumeration; an exotic one (cgo, unsafe
   arithmetic) gets a marker suite + an explicit deferral note.

## The arc's end-state claim (the honest ledger)

After this arc (user's formulation, the arc's law): **all bugs and
differentials are killed unless there is a profound reason they
exist.** Concretely: every baseline red is category-(b) frontier
(feature named, guardrails landed, on the frontier map) or
category-(c) profound-reason (ledgered, user-ratified at the gate);
every BUGS.md entry is fixed or category-(c); zero rows outside the
triage table. The starting category-(c) set — BUG-061's staticinit
residual + `init/hidden-dep-order` (optimizer-dependent init-order
latitude, L-011 — gc's own answer changes under `-N -l`) and BUG-059
(non-injective panic rendering) — is argued in the table, not
grandfathered: forcing those green against one compiler's optimizer
would be modeling gc, not Go — the doctrine's exact anti-goal. If
the user rules any (c) row insufficiently profound, it converts to a
fix obligation (this arc or a named successor).

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
5. The triage table complete: 13/13 open bugs + every baseline red
   in exactly one category; category-(a) rows fixed; category-(c)
   rows put to the user.
6. The frontier map + guardrail suite landed; every refused feature
   enumerated with oracle-verified cases classifying frontend-blocked;
   raft-path features at full enumeration depth.
7. The end-state claim verified against the final baseline: zero
   reds outside the triage table.
8. Untriaged-25 cross-check recorded.
9. `scripts/ci --diff` green at tip; every flip predicted; BUGS.md
   current; arc log (`docs/bugfix-arc-log.md`) current.
10. Pre-merge audit ASK posed (proposed size: 1 Opus reviewer for
   the frontend slices, 1 Fable reviewer for the semantic-core
   slice if BUG-005 is implemented — the interpreter is the primary
   dimension, always audited — and 1 Opus reviewer for the triage
   table + frontier map's honesty (every red truly categorized, no
   quiet grandfathering); Mike may trim/waive).

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
