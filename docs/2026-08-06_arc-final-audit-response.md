# Arc-final audit response — general-coverage (2026-08-06)

The arc-final pre-merge audit confirmed 21 findings (6 major, 6 minor,
9 note; 6 more refuted, no action). This note is the response record:
per-finding disposition, one commit per concern, guardrails first (59
red-first pins landed before any fix), full `scripts/ci --diff` + a
same-commit baseline re-pin at every movement commit, zero PASS→FAIL on
any pre-existing id anywhere in the series. Designated Surface/
Statements files are byte-untouched over the whole response (verified
by diff), so comparator-judge was not triggered.

Corpus: 966 → 1025 ids; pass 837 → 897; fail 129 → 128. Every one of
the 59 new ids is green at tip except the intentionally-red
`generics/local-type-argument`-class survivors listed under their bugs.
check-bugs: 21 entries, untriaged backlog unchanged at 15/15.

## Majors — all FIXED

- **F1 / BUG-015** (recover through synthesized promotion wrappers,
  the audit's top finding — silent wrong answer): fixed faithfully at
  the machine level per gc's own rule ("exactly one non-wrapper frame
  between gopanic and gorecover"). Declared wire-schema addition
  `"wrapper": true` on synthesized wrappers; `Func.wrapper` →
  `Cont.frame`'s trailing marker (default false — every pre-existing
  construction unchanged); `recoverResult`/`recoverThroughWrappers`
  skip wrapper frames, and ONLY the recover walk consumes the marker.
  Full lockstep: rules/stepFn wrapper-polymorphic (each pattern audited
  — optParam defaults silently narrow patterns to `false`), StateWf
  lemmas extended, MachineSound absorbed, WP frame laws generalized
  over the marker, golden repr baselines re-pinned for the schema
  addition. Pins: 4 divergences flip green; 4 controls hold
  (`interfaces/recover-promoted-wrapper/*`). Metatheory cost: moderate
  (one new walk helper + two StateWf lemmas + binder threading); no
  designated statement changed. Commit 785958e.
- **F2 / BUG-021** (append-spill envelope too narrow on the oracle):
  measured first (probe sweep, element sizes 1–40B, oldCap 0–1000,
  escaping/non-escaping); gc leaves growth+[0,8) in BOTH directions.
  Envelope widened to [newLen, max(32, 2·growth)] with the containment
  argument on `appendSpillUpper` (stack buffer ≤ 32 elements;
  size-class step < 1.5 < 2 above 32 bytes; spec floor newLen).
  Choice offset keeps the empty stream at the growth point → strict
  lane unchanged (zero drift outside the pins). Variable bound absorbed
  by the shared `applyStmtOp` + obliviousness kit; enumerator width
  metadata updated (`full-slice-cap-zero` width 32; eval pins → the
  32-member set). 3 membership pins (stack-buffer / below-formula /
  size-class regimes) flip green. Commit 5c08df2.
- **F3 / BUG-018** (local types in generic functions):
  `qualifiedTypeName` parameterizes function-local TypeIds with the
  enclosing instantiation's rendered args (ordered `curTargs` threaded
  through both stencil work kinds), matching gc's reflect spelling
  "box[int]"; duplicate-TypeId gate remains the collision boundary
  (cross-function same-name-same-args still refuses, probe-verified).
  2 differential + 1 export pin flip green;
  `generics/local-type-argument` stays red (M3's recorded refusal of
  the type-ARGUMENT direction). Commit f854483.
- **F4 / BUG-017** (mixed interface/non-interface comparison):
  emitBinary boxes the non-interface operand of mixed ==/!= (both
  orders); emitSwitch does the same at interface-tagged case slots
  incl. the reverse shape; untyped-nil comparisons unchanged. 7 pins
  flip (switch-on-any and the sentinel-error idiom included). Commit
  0e67e4e.
- **F5** (generic interface at enclosing type param poisons export):
  per-decl fix, not a refusal — anchors record the call site's stencil
  substitution and emit under it; `noteInterface` records interfaces at
  the active instantiation (substErr-protected); `substType` learned
  bare-interface method-signature substitution. Both pins (incl. the
  unrelated subject) flip green. Commit 3e536e3.
- **F6 / BUG-016** (untyped nil sinks): ONE mechanism —
  `wrapInterfaceConversion` (already at every assignable-context site)
  types untyped nil at direct slice/map/pointer targets; M1's
  map-literal special case folded in; spread calls routed through the
  same wrap. Func/defined/interface slots keep their disposition
  (BUG-014's boundary; its two pins stay red as recorded). 10 pins
  flip. Commit fb5f2c9.

## Minors — all FIXED (F8 = recorded narrowing, per direction)

- **F7 / BUG-019**: CLI renders "" for the canonical anonymous
  struct{} (the reflect.Name() contract); named empty structs keep
  names. 3 pins flip. Commit e2e32b5.
- **F8**: cap([]byte(s)) singleton narrowing RECORDED (probe showed
  gc's point is escape-analysis-dependent — cannot be matched
  statically): envelope statement + transfer caveat at the
  bytesFromString arm, doctrine gains a SINGLETON-NARROWINGS clause,
  green version-tracking pin (non-escaping point). Commit 405aa4e.
- **F9**: check-bugs ratchet extended to the `membership` stage
  (checks 4/4b), negative-probed on a scratch copy. Commit a67c241.
- **F10 / BUG-020**: identical-underlying pass-through arms for
  pointer/slice/map/func conversion targets (+ typed nils); rune/string
  conversions stay refused at the catch-all (real conversion logic
  owed, untriaged ids unchanged); tag-changing pointer shape stays
  fail-closed downstream at the struct-tag check. The mis-scoped
  "alias one cell under two tags" rationale corrected (F20). 7 pins
  flip. Commit 1792e2d.
- **F11 / BUG-012**: bare value-returning calls lower with typed
  discard temps at the decoder (decodeAssign's own mechanism, driven by
  resultTypes; .call and .callValue). 6 pins flip (chaining, helper,
  func value, multi-result, init()). Commit a8e2b3e.
- **F12**: composite-literal &T elision implemented via the shared
  hoisted-new helper (spec's own example shape included, pointer map
  keys included). 4 pins flip. Commit cd1031a.

## Notes — records corrected; F21 fixed forward

- **F13** wrapper second-drain comment: unsound safety claim replaced
  with the verified account + the required action if the shape becomes
  reachable. **F14** doctrine map-iteration envelope scoped to
  mutation-free iteration (BUG-005 cross-ref). **F15** signed-zero
  map-key retention: fifth (spec-SILENT) latitude point with transfer
  caveat. **F16** driver-copy rationale: slice-scoped fact retired; the
  standing no-driver-helper-in-GoCore POLICY recorded in CLI.lean, the
  membership note (dated addendum), and the eval-test header. **F17**
  floatvectors comment: overflow-span claim removed; actual coverage
  enumerated. **F18** arc-completion numbers made exact (31 re-pins;
  non-decreasing with four flat guardrail steps; arc-introduced vs
  pre-existing residual reds separated). **F20** struct-conversion
  docstring: embeddedness comparison is spec-EXACT, not a narrowing.
  (Commit f1271f4.)
- **F21**: DECIDED for the modern semantics — probe showed
  `GODEBUG=panicnil=0` flips GOPATH mode to Go 1.21+ behavior with no
  other effect (loopvar is language-version-driven and already modern),
  so the alignment is contained: `panicPayload` maps nil →
  PanicNilError, every oracle `go run` sets the knob, both pins
  re-pinned to the modern answers, §A2 superseded-addendum records the
  decision. Zero drift (model and oracle moved together). Commit
  a4ce5c5.

## Refuted (no action, per the dossier)

globals-outside-theorems; FloatBits TCB quantification; init-order
caveat placement; &&/|| RHS calls (recorded ANF decision);
imported-selector refusal message; goto-envelope conservatism.
