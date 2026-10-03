# The re-pin offer to the GoLean logic team (2026-10-03)

[AGENT] unit 7b worker, branch `docs/repin-offer-1003` (window plan `docs/2026-09-24_window-plan.md` row 7b; charter
`docs/2026-09-23_batched-window-charter.md` row 7). Authority: [USER] Mike 2026-10-03, verbatim, relayed by the [AGENT]
coordinator — cite as relayed: «prepare the offer, do the dry run». The [USER] is the user of all three teams: this is DESIGN
COMMUNICATION, not a negotiation. Nothing here merges, tags or pushes — the tag is the coordinator's at landing and stays
LOCAL (no push has ever been authorized). Evidence: `docs/evidence/2026-10-03_repin-offer/`.

## 1. The offer

- **The commit** `OFFER_COMMIT` — a placeholder for the SHA of this branch's tip as landed on `main`; the coordinator substitutes
  it at the train. Content = `main` @ `20d3946d` (train r61 close); this branch adds records only (`git diff 20d3946d OFFER_COMMIT
  -- GoLean tools scripts baselines` is empty). The local tag `logic-offer/2026-10-03` names it (charter row 7 spelled it
  `customer-pin/<date>`). Pin `provenance/pins.json` `golean.rev` to it; your Lean (`v4.32.2`) and Go (`c19862e5…`) pins are unchanged.
- **Green at the content tip.** `scripts/ci --diff` RESULT PASS, 3860/3860 rows against the baseline (3623 PASS / 237 FAIL, each
  FAIL on a `BUGS.md` Cases line), certificate provenance ok, semantic equations ok (commit `20d3946d`); charter row 7's three
  checks — STATEMENTS (`GoLean/GoCore/BridgeSet.lean`, 502 pinned rows, default build), EQUATIONS (`Equations.lean`, 293 proved,
  `scripts/check-equations`), the independent CLIENT (`Tests/EquationClient.lean`, 12 facts by the equation set alone, no runtime
  dependency, 12 gate self-tests + import whitelist); the core audit (classical trio only). The certified slow-tier record's
  receipt is at `44d99cdb` (train r61 step 5a); its observations are byte-identical to the pin's.
- **The frozen changelog** `docs/changelog/61958f2e-WINDOW.md`: its «Offer summary» is the cumulative before → after with the
  STATED LIMITS in one place; the per-lane rows below it are the window's records. In one breath: `Step` has a fifth index
  `StepLabel := {trace, picks, out}` and `stepFn` a fourth component; `Cont := List Frame` (the 33 old names as views; `Frame` 33
  incl. `preprintK`); `Step` 122 → 134 rules; `Func.wrapper` gone (promotion records; `Cont.frame`'s last field is the callee
  `FuncId`); every local position `VarId := Nat` with a checked name table; `Stmt.initialization` gone (block-entry allocation
  at `entrySlot`); `ChoiceSite.intn` new; `PanicEntry` gained `rewrite`/`repanicked` (the preprint phase renders `panic(err)`);
  `Store.alloc` normalizes and may refuse; the wire is `golean-native-v3` (v1/v2 refuse by name).

## 2. Your fixtures under this frontend (the inventory re-run; procedure of `docs/2026-09-24_customer-fixture-inventory.md`)

Source: `golean-logic` @ `8a572d2412bb986fe7f8a90a6b9b1562ba96b2c8` (`main`, 2026-10-03, clean; read-only — copied out). Units:
your 23 `examples/fixtures/*` (the fourteen of 2026-09-24 plus `abort-write`, `aggregates`, `integers`, `loops`, `observe-prefix`,
`perf`, `records`, `references`, `write-call-panic`) and the eight `f2` variants your `check_f2_proofs.py` generates (table
unchanged since `b2c37c1`; reproduced by the 2026-09-24 script). Frontend: `main` @ `20d3946d` (`tools/nativefrontend` subtree
`d2a64420…`, binary sha256 `6641453a…`), go1.26.5. **31 / 31 exported** (exit 0, stderr empty), all `golean-native-v3`; **1523
statement nodes counted recursively, 0 `"stmt":"unseq"`, 0 graph-body occurrences, 0 legacy `"stmt":"unseq-probe"`**; the
`--unseq-census` sweep reads `legacy` on all 1133 rows. Positive control, same binary and walker: `len-vs-call-order` 13 graphs /
6 probes, `e13-sibling-panic-order` 60 / 9, body kinds populated. Not established: your build or proofs (§5), fidelity (no
program executed here — §5's differential step is that), your source admission.

## 3. What you get against each request

**2026-09-23 §2, the five corrections.** (1) every `FinishOutcome` carries the endpoint store and residual tape
(`normal`/`deadlock`/`aborted`/`refused`/`fatal`); `run_panic_iff`. (2) `Finish.aborted`/`refused` require the SETTLED `abort?`,
the `consumeAtE .repanicCollapse` draw and the fallible `abortMsg`; `fatal` covers the preprint fatal. (3) `ZeroCost` at cost 0,
the abort at cost 1; `run_ok/panic/deadlock/fuelOut_iff` (fuel-out = the fixed tape's actual prefix of length `fuel` with no
zero-cost finish); `prefix_refl/comp/split/erase_*/iter` for every `n`; the four boundary controls. (4) `replays` by record,
`finish_replay`, `replay_coverage` PREMISE-FREE. (5) `classification` unconditional over four disjoint cases, `classification_wf`
the domain corollary; `NoRefusal` sequential-only. **§3 labels.** `{trace, picks, out}`, ordered per channel and across steps,
no total interleaving (documented); `fold` + `fold_silent` (no `[emptyLabel]`); `stepThread_privateStep_label`, `PoolProjection`;
`initPrintRefusal?` RETAINED; call/return cuts through the frame's `fid` + `frame_exit_returns` — `out` is printed bytes, not a
`Ready` event. **§4 conditions.** P: receiver once, pointer/value adjustment, embedded traversal, nil behaviour, qualified
identity, method-value capture at creation, direct-`recover` eligibility PRESERVED (rows 65–89; `methodInfoByFuncId?` unchanged).
B6: declaration ids + the checked table (`Func.localsOk`), lexical id ≠ activation slot (`bindParams_lookup`,
`enterFrame_lookup_arg/_result`); ids stable across edits are NOT an API promise. C4: allocation separate from initializer
execution; `entrySlot` as the stated function; lifetime lemmas (`blockEntry_fresh`, `pushDefer_saves_values`,
`funcVal_captures_locs`, `frameEntry_fresh`); the preservation claim SCOPED (injection + stuttering, escape audit first) — a
stated claim, not a theorem. C1: the normalization premise (`Store.alloc`, `HeapNormal`), `loadRoot_base`, `storeLoc_root`,
`Store.alloc_shape/_cell`, `Heap.lookup_set_self/push_self`; the memory FLOOR is limit 1. **§6.** BridgeSet 502 rows (statements
AND equations); the `stepFn_eqns` rewrite set (premised arms by instantiation or `simp (discharger := assumption) only
[stepFn_eqns]`); the toy client; the gate's twelve fail-closed self-tests; the changelog frozen; the receipt.

**2026-09-28 note, requests 1–9.** (1) PARTIAL with the floor stated — variable reads → `loadRoot`, plain/chain stores →
`storeLoc`, block/frame entry → `Store.alloc`; `*p`/`x.f`/`a[i]`/map reads stop at `applyStrictOp`/`applyRhsOp`; the filing
correction made (`callArgsK`, `callValCalleeK`, `callValArgsK`, `deferCalleeK`, `deferArgsK`, `stmtOpK` are `.retV v` arms).
(2) `runProgramSetup_noInit` + `setup_lookup_arg/_result`, `setup_resultLocs`, `setup_heap_size`; residual tape = input tape.
(3) rows 108–132. (4) rows 136–154 (`entrySlot` for both entries; the lifetimes). (5) rows 65–89 incl. `enterFrame_declared`,
`receiverAt_nil_path`, `resolveMethod?_declared`; the narrowing bridge `findFunctionIn?_filter`. (6) the frame field `fid` +
`frame_exit_returns` ([USER] 2026-09-28, option 1; label shape unchanged). (7) `panicking_glue`/`_seq`/…, `next_panicResumeK_unrecovered`,
`panicking_frame_defer*` (the `deferPanic` entry), `panicking_frame_empty`, over the preprint arms too. (8) the cumulative tool-interface
table (flags 8 → 9: `-unseq-census`; the rest unchanged). (9) `execProgLoop_single_noBoundary` (+ `_wide`): equal fuel when no boundary opens.
**Route A (2026-09-30), post-window.** Your §5 requirements (a named `FuncId` list; hash-pinned generator output; plain indexed
loops / `break` / `continue` / depth-bounded recursion / no reflection; the init-time pick in ONE `mapIter` shape; a documented
footprint) are carried in the lane brief (`subject/protobuf-route-a`; go-ahead PENDING [USER] at dispatch). Your §4 caveat is answered
in the window: BUG-004 item 4 landed (row 6b) with `renderPanicHead_text`/`abortMsg_text`/`stepFn_text_abort`/`runConfig_text_abort`
and their refusal twins (rows 155–173).

## 4. Stated limits (the summary's ten, one line each)

(1) the memory floor; (2) the pool/registry half OWED; (3) the legacy triple survives (`cases` arms only for your fragment); (4) C4's
run-level simulation is a stated claim, not a theorem; (5) raw location ids in the readout JSON; (6) setup is a premise
(`runProgramSetup_noInit` is its no-globals case), init-time printing refused; (7) `NoRefusal`/classification sequential-only, a
refusal has no successor; (8) the corpus limits (Storage is a program; `time`/`rand.New` refused by name; access labels not a
differential observable; loops/`range`/goroutines/route A post-window); (9) deferred: NaN, E6b–e, route A, the `unseq` commutation
theorem (confluence WITHDRAWN), NPDRF unusable, typed profiles parked; (10) the lowering carries no correctness theorem. Charter
§2 tail: the restricted sequential result does NOT discharge the whole owed simulation.

## 5. The dry run (evidence, NOT your acceptance)

Offline setup: `git clone --local` of your `main` @ `8a572d24` into OUR gitignored `deps/`; the ONE edit `provenance/pins.json`
`golean.rev := 20d3946d…`; `scripts/setup --golean-source <our repo> --reference-root <our deps> --dependency-seed <your packages
dir>` — local clones, copied caches, no network, «Exact live dependency checkouts verified». Build: your gate's `lake build
GoLeanIris GoLeanIrisExamples GoLeanIrisAudit GoLean.NativeToIR` under `scripts/capped` (48G, 6 threads, the box-wide lock),
142 s, EXIT=1. **GoLean itself built with zero errors** (26 modules incl. `Machine`, `StepFn`, `MachineSound`, `MultiSound`,
`NativeToIR`). Of your 242 enrolled modules + 4 consumer libraries: **6 built, 28 failed on their own errors, 212 blocked** by a
failing import (189 via `GoLeanIris.Language`; the consumers via `Logic.Public`). 22 of the 28 are generated `*Program.lean`
artifacts («Do not hand-edit the emitted body» — your `tools/emit-native-program.lean` regenerates them from the wire at gate
time); 6 are hand-written (`Language`, `Logic.StepAdapter`, `Logic.FrameCont`, `Logic.Direct`, `Logic.Binding`, `Logic.Source`).
1864 error blocks; 16 artifacts truncated at Lean's `maxErrors` (lower bounds). By cause (`dryrun-error-census.tsv`):

| Cause | Blocks | Where (frontier) | Answered by |
|---|---|---|---|
| `VarId := Nat` — `"p"`/`"$c0"` where a `VarId` is expected; `Scope`/`LocalEnv` no longer `List (String × Loc)`; your `environment`/`materialize`/`Γ.bind` cascade | 1568 | 22 artifacts + `Binding`, `Source`, `Direct` | row 5 — B6; pins 108–132 |
| `Func.wrapper` deleted — `wrapper := false` in `Func` literals, `f.wrapper` projections, `⟨…, false, false⟩` positional (the sixth field is now `locals`), `Cont.frame … (wrapper : Bool)` → `FuncId` (`FrameCont.lean:23`) | 140 | 22 artifacts + `FrameCont`, `Source` | row 3 — P migration table; pins 13, 65–69; `methodInfoByFuncId?` unchanged |
| `Stmt.initialization` deleted — every local's declaration in the artifacts; your `Statement.erase` (`Source.lean:1340`, `:1403`) | 129 | 18 artifacts + `Source` | row 6 — C4; pins 136–154 |
| the label — `stepFn … : Except Stop (Config × Store × Choices × StepLabel)`, `Step … : StepLabel → Prop` (`StepAdapter.lean:29–51`, `Language.lean:34–55`; your adapter's docstring anticipates it) | 11 | `StepAdapter`, `Language` | shapes rows 1–3, row 2a; pins 1–2, 22, 25–28, 35–64 |

NOT OBSERVED here because the modules that would meet them are blocked (expected per the changelog; listed so you can plan): `cases`
on `Cont` as a list (row 4), `Store.alloc`'s `Except` (C1), the new `Frame`/`Step`/`ChoiceSite` arms in exhaustive matches (rows 5b,
6b), `PanicEntry`'s anonymous constructor, the settled-chain premise on `abort?`/`step_abort_elim` (row 6b), `enterFrame`'s `Entry`
outcome, `stepFn_consumption_some'` → `stepFn_consumption_some` (row 7a), your emitter against the v3 wire (`Func.locals`, numeric
ids, `.block` declarations, `promotions`). Your gate's one Lean-independent step — `differential` (`scripts/diff-coverage` over your
`manifest.tsv`, in the dry-run workspace with the `golean` CLI built from our main, your gate's env) — is **18/18 PASS,
export_status=0** (`dryrun-differential.txt`): the manifest schema is unchanged; your fixtures' observations agree with go1.26.5.

## 6. The acceptance boundary

A dry-run `lake build` is evidence, not acceptance (your response §6): the port is accepted on YOUR side only after `scripts/check`,
the initialized/all-choice theorems, the native edit/mutation controls and all three isolated consumers pass; `scripts/ci` is ours.
The historical package's pin and status stay intact. Row 7b completes when this branch lands with the tag; the limits are the summary's.
