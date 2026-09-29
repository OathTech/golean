# Method promotion (G-P, window row 3) — lane handoff

Lane `core/method-promotion-0928`, worktree `.claude/worktrees/method-promotion`, off main `89792db1` (train r53 close).
Specification: `docs/2026-09-28_gp-method-promotion-design.md` (G-P PASSED, all ten §6 decisions as recommended — [USER] Mike
2026-09-28 «Go ahead and land, and approve the decisions as proposed», relayed by the [AGENT] coordinator; rulings ledger
«G-P (native method promotion) passed»). Writer: [AGENT] worker. Any deviation from a ruled decision is a new design gate:
posed in §3 below, that item STOPPED.

## 1. State per slice

| Slice | Tip | Gate | Rows born / moved | Status |
|---|---|---|---|---|
| S0 born pins | (this commit) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` RESULT: PASS, 788 s, 3784/3784 FULL no regression (dirty-tree note: the run preceded the commit; the committed tree differs from the gated tree by one ledger citation re-spelling, see §4) | 16 born (13 PASS, 3 FAIL by design); 0 moved | DONE |
| S1 records + cross-check | (this commit) | individual gates all EXIT=0 (`check-wire-boundary` 3 s incl. the 12 new controls, `check-frontend-pins` 2 s after the twin re-pin, `check-unseq-wire` 6 s, `check-method-identity` 46 s, `check-mem-callsites` 1 s, `check-unseq-scheduler` 92 s, `check-core-audit` 20 s, `gocore-eval-tests` 296 ok / 0 fail, `go test ./tools/nativefrontend ./tools/lowerdiag` ok); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` RESULT: FAIL, 1132 s, by EXACTLY the expected merge-protocol 5a pair and nothing else — `certificate provenance` STALE (changed compiled inputs: `GoLean/GoCore/{Syntax,ProgramCtx}.lean`, `GoLean/NativeToIR.lean`) + ONE row `imported-goose/channel/google-search` PASS/membership → FAIL/membership («certified record wire-sha256 … STALE»: the row's wire gained `promotions`, 736f1730… → 8fe3c739…); 3784 = 3544 / 240 vs baseline 3545 / 239, every other step ok, negative 394 match, re-pin guard 0 flips; `baselines/certified/` NOT re-pinned (the train's 5a step) | 0 born; 0 moved (the machine is unchanged; the whole-corpus choice trace is byte-identical to the S0 reference — §1 S1) | DONE (S1 tree) |
| S2 the switch | (this commit) | individual gates all EXIT=0 (`check-core-audit` 13 s — 88 required theorems, `check-mem-callsites` 1 s, `check-unseq-scheduler` 96 s, `check-wire-boundary` 3 s incl. the 12 promotion-record controls (3 new), `check-unseq-wire` 6 s (140 fixtures regenerated), `check-frontend-pins` after the twin re-pin, `check-method-identity`, `gocore-eval-tests` 298 ok / 0 fail (incl. the two new v2 refusal pins), `go test ./tools/nativefrontend ./tools/lowerdiag` ok); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` RESULT: FAIL, 1006 s, by EXACTLY the expected merge-protocol 5a pair and nothing else — `certificate provenance` STALE (C9: the first changed compiled input, `GoLean/CLI.lean`) + the ONE drifted row `imported-goose/channel/google-search` PASS/membership → FAIL/membership (its certified record STALE since S1); 3784 = 3548 / 236 vs the re-pinned baseline 3549 / 235, every other step ok (core build warning-free, 88 required theorems, eval 298 ok, negative 394 match), re-pin guard 0 PASS→non-PASS flips / 4 GREENED; `baselines/certified/` NOT re-pinned (the train's 5a step) | 0 born; 4 moved, all FAIL → PASS: the design's three predicted flips — `race/free/promoted-ptr-hop` (decision 6), `embedding/promoted-ptr-method-expression/{recover,promoted-value}` (decision 5) — PLUS `noodler/frontier/promoted-method-expression-ptr` (FR-3's noodler re-hit, the same `(*T).M`-over-promoted class the design did not enumerate; attributable to decision 5; found by the choice trace, confirmed by `diff-one`, reported for the audit); 3784 = 3549 / 235; the whole-corpus choice trace vs the S0 reference: BYTE-IDENTICAL dumps and results EXCEPT the rows of the four flipped ids (`race` → `ok`; `unsupported` → `ok` ×3) and the known absolute-path row (§1 S2); detector-soundness HOLE 0 / possible-HOLE 0, `promoted-ptr-hop` agree-DRF (was over-refusal) | DONE (S2 tree) |
| S3 equations + records | (this commit) | individual gates all EXIT=0 (`check-core-audit` 16 s — **110 required theorems** (88 + 22), `check-mem-callsites` 0 s, `check-unseq-scheduler` 96 s, `check-wire-boundary` 27 s, `check-unseq-wire` 5 s, `check-frontend-pins` 1 s, `go test ./tools/nativefrontend ./tools/lowerdiag` ok under ci's `GO111MODULE=off`); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` under the lock RESULT: FAIL, 1035 s, by EXACTLY the expected merge-protocol 5a pair and nothing else — `certificate provenance` STALE (the reconciler's C9 names the first changed compiled input, `GoLean/CLI.lean`; the certification controls all PASS) + the ONE drifted row `imported-goose/channel/google-search` PASS/membership → FAIL/membership (its certified record STALE since S1); 3784 = 3548 / 236 vs the S2-pinned baseline 3549 / 235 — IDENTICAL to S2's count, that one row the whole difference; every other step ok (core build warning-free, eval 298 ok, negative 394 match), re-pin guard 0 flips (the 4 GREENED notes are S2's re-pin, HEAD vs HEAD~1); `baselines/` untouched | 0 born; 0 moved (S3 changes no definition: every row in its S2 lane) | DONE (S3 tree) |

### S0 — the born pins

Every expected value observed under go1.26.5, plain and `-race`, before the row was written; `scripts/diff-one` on the 16 rows at
the S0 tree (main's code — S0 changes no code), then the full gate.

- `embedding/promoted-dynamic-surface/` (11 rows, all PASS on main): `go-nil-ptr-embed`, `go-nil-iface-embed` (PASS/confluent —
  the path is walked in the CHILD, the parent's recover never fires, gc aborts with the nil-dereference text); `defer-nil-path`
  (107 — walked at the drain), `defer-box-mutated` (2), `defer-static-control` (1 — the static control), `defer-ptr-hop-replaced`
  (3), `iface-method-value-late` (25), `iface-method-value-ptr-hop` (4), `defer-method-expr-recover` (0 — `defer S.M(s)` recovers
  in the promoted method), `defer-method-expr-recover-status` (ok 0), `nil-box-ptr-method-value-embed` (100 — `&nil.f` panics).
- `embedding/promoted-ptr-method-expression/{recover,promoted-value}` FAIL/frontend-export by design (the `(*S).M` deref-adapter
  refusal over a PROMOTED value method; gc 0 and 2) — on the ledger's FR-3 line; the refusal retires for promoted entries at S2
  (design §2 S7, decision 5). Not wrong answers: fail-closed refusals, rowed at detection.
- `race/free/promoted-ptr-hop` FAIL/confluent by design (BUG-041's Cases: line — the S3 addendum's predicted embedded-pointer-hop
  over-refusal; gc `-race` green 5/5) and its must-stay-racy guards `race/negative/{promoted-ptr-hop-target,
  promoted-ptr-hop-field}` PASS/racy (gc `-race` reports both). The free row is expected to flip at S2 (decision 6).
- No wrong answer found on main: no BUGS entry filed; BUG-041 gained the born row and a dated paragraph.
- Records: baseline header entry + 16 rows (3768 → 3784 = 3545 / 239); `docs/language-coverage-ledger.md` FR-3 row (2 → 4),
  queue row 3, Q-RACEPATH row (1 → 2), §8 tally, reds table (frontier 128 → 130, Q-* 9 → 10, total 239), movement §8an.

### S1 — the records and the cross-check (additive; the machine is unchanged)

Design §5 S1, §4 (the wire), §2 S2 (b) (the validation). Every ruled decision followed as recommended; no deviation.

- **Frontend** (`tools/nativefrontend/emit.go`): `synthesizePromotionWrappers` now returns the wrappers AND one promotion
  record per promoted method-set entry (`promotionRecord`, `promotionStubRecord`), built from the SAME `types.NewMethodSet`
  selection as the wrapper/stub, in the same pass and order (instantiated structs included — design S10); the program
  gains the REQUIRED top-level `promotions` array (`[]` when the package promotes nothing). The wrappers and stubs are
  byte-identical to S0's. Record shape per design §4: `{type, member, inPtrSetOnly, path:[{owner, field, ptr}], adjust ∈
  asIs|deref|addr, target: {method: FuncId} | {iface: TypeId}, unsupported?, sig?}` — `sig` (the `MethodSig` shape of
  interface requirements, `sig.id = member`) is read off the stub map itself, so it equals the stub's by construction.
  Self-check: go/types' set answer must equal spec#Struct_types' rule (`*T`-only ⟺ pointer-receiver target ∧ no
  embedded-pointer hop) — a disagreement refuses the export (new `unsup` texts all begin `promoted …`, the
  lowerdiag `expression-shape` class; `TestVocabularyCoverageIsTracked` green).
- **Core data** (`GoLean/GoCore/Syntax.lean`, beside `MethodSetRecord`): `PromotionAdjust`, `PromotionHop`,
  `PromotionTarget`, `Promotion`, and `Program.promotions : Array Promotion := #[]` (docstrings cite the design note);
  `ProgramCtx.promotions` (`GoLean/GoCore/ProgramCtx.lean`). NO machine consumer in S1: `stepFn`/`Step`, `Ops.lean`,
  `Machine.lean` untouched. Every existing `Program` literal compiles unchanged (the field is defaulted, last).
- **Decoder** (`GoLean/NativeToIR.lean`): `decodePromotion` (exact-key sets on the record, its hops and its target;
  `unsupported`/`sig` present exactly together), `validatePromotion` (the design's S2 (b) checks: hop-by-hop embedded
  field of the previous hop's struct with `ptr` against the field's type, an intermediate hop into an imported/opaque
  owner refuses; the last hop's type = the target's receiver base or the interface itself; member identity = the
  target's, package-qualified, and `sig.id = member`; `inPtrSetOnly` re-derived from spec#Struct_types; `adjust`
  re-derived from the last hop's kind and the target's receiver; a record's `(type, member)` that is a DECLARED method
  of the carrier refuses), duplicates refuse, and **the S1 cross-check**: the carrier's method `methodFuncId type member`
  must be the record's wrapper — `Func.wrapper = true`, receiver kind = `inPtrSetOnly`, exactly one forwarding call whose
  callee is the record's target (the declared method's FuncId, or `methodFuncId iface member` for an interface target)
  and whose receiver argument EQUALS the `Expr` chain the record denotes (`promotionRecvChain`: the decoded form of
  `fieldPathValue` / `fieldPathAddrFrom` / `valueRootedFieldAddr`), the other arguments forwarded 1:1 — or, for an
  `unsupported` record, the declaration-only stub carrying `frontend-quarantined: <the record's cause>` and exactly the
  record's `sig`; and every `Func.wrapper` has a record (the reverse direction). One rule beyond the design's letter
  ([AGENT], recorded here for the audit, not a deviation from any §6 decision): a `method` target with NO declaration on
  the wire is accepted iff the reached type is an imported/opaque declaration AND the target key is exactly
  `methodFuncId reached member` (the key pins the receiver base and the member; the receiver KIND is read back from the
  record's `adjust` and the wrapper cross-check decides). This is the raft twin's `raft.DefaultLogger.output` → the
  UNEXPORTED `log.Logger.output`, which the imported stub pass does not carry (contract note §5) while go/types promotes
  it; today's wrapper forwards to the same absent key (a dispatch would go stuck). A locally declared reached type
  refuses (D2: its full table is on the wire). In the corpus 0 records have an absent target; the twin has this one.
  **S2 note**: at the switch, a record whose target has no `Func` must make the CALL refuse by name (today: stuck).
- **Controls**: `scripts/check-wire-boundary` gains 12 promotion-record controls through the real CLI over the new
  fixture `Tests/wire-boundary-promotion/main.go` (`probe` answers 42; the positive control) — the field absent, a
  non-embedded hop, a wrong `ptr`, a wrong `inPtrSetOnly`, a wrong `adjust`, a target identity mismatch, `sig` without
  `unsupported`, a wrapper body that disagrees with its record, a wrapper without a record, a duplicate record, a record
  naming a DECLARED method — each refused by name. Go unit tests `tools/nativefrontend/promotion_test.go` (value embed,
  pointer embed, two hops, pointer embed of the declaring type (`deref`), an embedded interface field, `*T`-only entries,
  the sync stub, the FR-23 stub, a generic instantiation, the empty array; plus the wrapper↔record pairing check on each
  wire). `Tests/GoCoreEval.lean`: an in-process pin that a wire without `promotions` refuses naming the field.
  Hand-built wires gained `"promotions":[]`: 11 strings in `Tests/GoCoreEval.lean`, 1 in `Tests/MethodIdentity.lean`,
  and the 140 `Tests/unseq-wire/*.json` fixtures REGENERATED by their generator (`build.py --frontend <new frontend>`;
  each +1 line, `build.py --check` green inside `check-unseq-wire`).
- **The twin pin** (`baselines/pins/twin-chdriver.wire.json`): 1c4e7038… → 7e8c06e6…; 56 records = 53 wrappers + 3
  promoted sync stubs (exactly the design §4 prediction); EVERY other top-level key identical (a key-by-key JSON
  comparison); written reason in the `scripts/check-frontend-pins` header. The twin decodes under the new decoder
  (probed through the CLI: a nonexistent-function stuck AFTER decoding). Not re-run under the machine (40–65 min; the
  machine reads nothing from the records in S1).
- **Measurements** (the S1 frontend over the whole corpus, `scripts/choice-trace-corpus` export, 2026-09-28): 3784
  manifest rows, 2 excluded (the reference's exclusions), 34 frontend refusals (the SAME ids as the S0 reference), 3748
  wires; **221 wires carry 867 records = 805 wrappers + 62 stub records (the stubs in 23 wires)**; 134 `*T`-only entries,
  99 interface targets, hops 1/2/3 = 719/145/3, adjust asIs/addr/deref = 616/143/108. Every S1 wire equals its S0
  reference wire in EVERY top-level key except the added `promotions` (3748/3748). (The design note's 2026-09-28 count,
  678 wrappers in 182 wires, was over the r52 lane's 3732 wires; the corpus has grown since.)
- **Zero behaviour change** (design §5's criterion): the whole-corpus choice trace with the S1 binary
  (`scripts/choice-trace-corpus --dump --jobs 6 …`, the reference's exact command and exclusions, both under the lock)
  — every per-consumption dump row and every result row `LC_ALL=C sort`ed and `cmp`ed against the S0 reference run
  (`.claude/worktrees/method-promotion-ref/.tmp/ct-ref/`): RESULT: the per-consumption DUMPS are BYTE-IDENTICAL (26 367 rows, 1 976 565 bytes); the RESULTS are BYTE-IDENTICAL (22 489
  rows) after normalizing the ONE row on each side that embeds the run's absolute `--out` path (the decoder's refusal text for
  `arrays/materialization-budget/over-budget` names its input file); `exhausted-confluent.tsv`, `exhausted-strict.tsv`,
  `excluded.tsv` identical; the same 34 export-refusal ids; the summarizer's output identical modulo that path (and its
  fixed-column truncation of that one line). Both runs exit 1 «FINDINGS present» — the summarizer's standing findings,
  identical on both sides; the evidence is the byte identity, not the exit code.
- **The full gate** (`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow`, the wire/decoder slice — merge-protocol 5a
  class): RESULT: FAIL, 1132 s, by exactly the expected 5a pair (the S1 row above): `certificate provenance` STALE (the
  reconciler's C9 names the first changed compiled input, `GoLean/GoCore/ProgramCtx.lean`) and the ONE drifted row
  `imported-goose/channel/google-search` (PASS/membership → FAIL/membership, reason «certification: certified record
  wire-sha256 missing, duplicated or STALE»). The tier=slow re-certification produced NO fresh candidate:
  `tools/certification.py enumerate_record` checks the tracked record's `# wire-sha256:` header BEFORE enumerating and
  refuses STALE (the header holds 736f1730…, the S1 wire is 8fe3c739…), so the fresh run and the candidate install are
  the train's 5a step (design §4: «train step 5a re-certifies … a provenance refresh, not a claim change»);
  `baselines/certified/` untouched here. Every other ci step ok (incl. the reconciler's C13 — pre-existing doc-site Go
  versions, report-only, not this lane's). The S1 tree is committed after the gate; the committed tree differs from the
  gated tree by THIS records file only (§4).

### S2 — the switch (the machine consumes the records; the wrappers are gone)

Design §5 S2, §2 S1–S10, §3, §4 (decisions 1–10 as recommended, [USER] 2026-09-28 relayed); PLUS the coordinator's
[USER]-ruled addition, quoted verbatim as relayed to this worker ([AGENT] lane worker → [AGENT] S2 sub-worker,
2026-09-28): «Coordinator addition, [USER]-RULED ([USER] Mike 2026-09-28, verbatim, relayed: «Agree on (1)» — the logic
team's request 6, option 1): frames record which function they belong to. In the same reshape where you delete
`Cont.frame`'s `wrapper` field, add a field carrying the callee's `FuncId` (set by `enterFrame` from the `fid` it
resolves), so a client can observe "f returned v" from the configuration at frame exit. It is a representation field
only: no behaviour change, the `StepLabel` shape unchanged (option 2, a call/return label channel, was NOT taken).
Expose a lemma stating the field at frame entry (e.g. via `enterFrame_declared`) and one at exit, pin both in
`BridgeSet.lean`, add them to the core audit's required list, and record the field in the changelog (constructor
shape before → after, what a re-pin touches).» — DONE in S2 (below). No deviation from any ruled decision; the
[AGENT] choices the design left open are listed.

**What shipped** (the migration table is the changelog's row-3 section; every replacement NAMED, no alias):

- **Core resolution** (`GoLean/GoCore/Ops.lean`): `methodDecl?` (depth-0 declaration lookup, the former `direct`
  fold), `promotion?` (the record lookup), `resolveMethod?` (replaces `concreteMethodForDynamic?`; answers a
  `MethodResolution {path, adjust, target, inPtrSetOnly, unsupported, sig}` — declared = empty path with `asIs`, or
  `deref` on the `*T ⊇ T` arm; promoted = the record's, admitted into the value set only when `¬inPtrSetOnly`
  (spec#Struct_types); the arms are disjoint because the decoder refuses a record naming a declared method),
  `resolvedSignature?` (+ `funcSignature?`, replacing `concreteMethodSignature?`) under `satisfiesMethodSig` and
  `hasNoArgStringMethod` (S9: a stub record's `sig`, a declared target's `Func`, an embedded interface target's
  `MethodSig`). `nilValueMethodText?` and `ChoiceTrace.nilTextFacts`: the family test is «the resolution path is
  empty» (S9); the site's width and consumption are identical (the trace comparison below).
- **The path walk** (`Ops.lean`): `WalkCursor` (`val v | cell l`), `structFieldValue`, `promotionHop`,
  `promotionWalk`, `receiverAt root path adjust` — the receiver the target takes and the walk's LOADS (S3/S4/S8):
  a value hop projects (no read), an embedded-POINTER hop reads the pointer field, a value receiver at the end of
  the path reads its cell, `deref` copies the pointee out, `addr` takes the reached cell's address; a hop through
  `nil` and a value receiver out of `nil` panic with the nil-dereference text, a final pointer receiver through a
  nil embedded `*E` receives `nil`. The EMPTY path is the direct dispatch (`asIs` = identity, `deref` = the one
  pointee read — today's `*T ⊇ T` arm, unchanged). `dispatchLeaf`, `wrapperForwardArg`, `recvFieldChain` DELETED.
- **Dispatch** (`dynamicDispatch?`, `Ops.lean`) answers `Dispatched.target func args | again fid args` (S5): a
  path ending in an embedded interface field re-dispatches on the field's value through the interface's anchor
  `methodFuncId iface member` as the NEXT step. A stub record (`unsupported`) refuses BY NAME with the frontend's
  cause (`frontend-quarantined: …`, the decoder adds the marker exactly as the retired stub body carried it) — after
  the ONE check the retired stub's entry made before its body: a `.nil` pointer box to a value-set entry panics
  first (the retired auto-deref; `inPtrSetOnly` entries refuse). A promoted target with NO `Func` on the wire (the
  twin's `raft.DefaultLogger.output` → unexported `log.output`) refuses BY NAME (`unsupported`: «has no declaration
  on the wire … refusing rather than dispatching from no body») where the retired wrapper went stuck (S1's note).
  The declared arm looks the target up BEFORE the receiver read (the order `nilValueMethodText?` mirrors); the
  promoted arm walks first, then finds the target (the retired wrapper's order).
- **Entry** (`Machine.lean`): `Callee (func | promotion)` and `callee?` (S7: `S.M`/`(*S).M` over a promoted entry
  name the record; `promotedCallee` applies the path to argument 0, whatever its form — value or pointer — so the
  `(*S).M` deref-adapter refusal retires for promoted entries), `Entry (run func frameEnv resultLocs | again fid
  args)`, `enterFrame.plan : … → Except Stop (Commit (Entry × Store × AccessTrace))`, `Entry.callConfig plans env k`
  (the CALL positions: `run` → the frame; `again` → `.retV (.funcVal fid args) (.callValCalleeK plans [] env k)`,
  the same position re-entered next step) and `Entry.drainConfig barrier requeue` (the DEFER drains: `run` → the
  barrier frame; `again` → the draining frame with `(.funcVal fid args, [])` at the head of its chain; the SPAWN
  child: `.next (.frame [] [] [] [(cv, [])] .stop fid)`). All 6 `Step` entry rules, the 6 `stepFn` arms and
  `spawnStep` deliver through these two functions.
- **`Cont.frame targets tenv results defers k (fid : FuncId)`**: the wrapper `Bool` DELETED, the callee's `FuncId`
  ADDED in its place (the coordinator's addition). [AGENT] choice: the field is the id of the function WHOSE BODY THE
  FRAME RUNS — the declared target `enterFrame` actually enters (`Entry.run`'s `func.id`), never an interface anchor
  or a record (for a promoted dispatch the anchor is not a function with a body; the record is not a function); the
  drivers' barrier frames name the entry point / `pkgInitFuncId`; the spawn's `again` barrier frame names the anchor
  the `go` statement re-dispatches through (that frame belongs to the goroutine's call, whose callee is that anchor).
  Position: the LAST field, where the wrapper marker stood, so every `.frame t e r ds k w` pattern keeps its arity
  (the universally quantified `w` became `fr : FuncId` in the rules — no rule reads it). Lemmas: `Entry.callConfig_run`
  (the frame a call position pushes names the resolved callee — definitional), `frame_exit_returns` (a frame exit
  from `.frame … fid` reads its pinned results as `vs` and resumes the caller on its targets, both entries:
  «`fid` returned `vs`»), `enterFrame_declared` (design §3: a declared, non-anchor callee's entry IS bind/declare/pin
  into a frame naming `func.id`, no dispatch, no memory access — the `MaybeUpdate` shape) — pinned as BridgeSet rows
  65–67 (RE-PIN 3, with rows 11/13/15 re-pinned over `Entry`/`FuncId`), added to `Tests/GoCoreAudit.lean`'s required
  list (85 → 88).
- **Recover** (S6, decision 7 — the DIRECT form shipped, not the glue-skip fallback): `recoverAtDeferred` (the
  deferred frame sits directly on the unrecovered `panicResumeK`) replaces `recoverThroughWrappers`;
  `Cont.recoverTransparent` deleted; `recoverResult` descends `Cont.isGlue`. The well-formedness lemma
  (`recoverAtDeferred_locSup`, `recoverResult_locSup`) was NOT costly. `interfaces/recover-promoted-wrapper/*` (8
  rows) hold.
- **`Func.wrapper` DELETED** with every consumer: `SyntaxEqb.Func.eqbF` (6 → 5 conjuncts), `Admission.BooleanSyntax`
  (the conjunct gone; `admitted_all_bodies`' projection), `MachineEqb` (the frame's `FuncId` compared),
  `EnumDedup.contDepth`, the decoder. Proofs repaired: `StateWf` (`dynamicDispatch?_locSup` over `Dispatched`,
  `promotedCallee_locSup`, `receiverAt_locSup`/`promotionWalk_locSup`/`promotionHop_locSup`/`structFieldValue_locSup`,
  `enterFrame_wf` over `Entry.locSup` with the arm macros `enterFrame_run_arm`/`enterFrame_again_arm`,
  `Entry.callConfig_bounded`/`drainConfig_bounded`, the seven entry cases of `step_preserves_wf_loc`),
  `MachineSound` (the entry destructurings and the `stepFrameExit` binder), `MultiWfSound.spawnStep_wf`,
  `Multi.spawnStep_oblivious`, `PrefixFacts`, `StepErrors` (`promotionWalk_tame` leaf, `runCommit_of_entry`),
  `Tests/GoCoreContract.lean` (`recover_bare`/`recover_handler` by `rfl` over `recoverAtDeferred`; the audit frames
  name `auditFid`), `Tests/MethodIdentity.lean` (`nil_text_ignores_foreign_wrapper` →
  `nil_text_ignores_foreign_declaration`, `nil_text_does_not_borrow_foreign_body` →
  `nil_text_promoted_entry_outside_family` — a promotion record is outside BUG-087's family; `Tests/MethodIdentityAudit.lean`
  follows). `stepFn_sound`/`step_complete` in the same tree. No `sorry`/axiom/`native_decide` in `GoLean/`, no
  `partial` in `GoLean/GoCore/`; the core build is warning-free.
- **Frontend + wire v2** (`tools/nativefrontend/emit.go`): schema `golean-native-v2`; `promotionRecords()` (one
  record emitter) replaces `synthesizePromotionWrappers`/`synthesizeWrapper`/`syncPromotedStub`/`promotedSigStub`
  (and `valueRootedFieldAddr`, used only by the wrapper); the promoted sync-primitive and FR-23 stubs are
  `unsupported` + `sig` RECORDS (`promotionStubRecord`); the signature is still EMITTED per entry
  (`promotionSignature` — the retired wrapper's own emission of receiver/params/results — so every type the
  signature mentions is registered as before and its `unsupported` refusal is the FR-23 probe); an embedded-interface
  target registers the interface's own method set and the anchor (`noteInterface`/`noteCalledIfaceMethod`, the
  retired forwarding call's registrations, BUG-095's static-interface rule kept). The FR-23 stub cause reads
  «promoted method T.M (promoted signature does not lower: …» (was «forwarding wrapper not synthesized: …») — the
  one refusal TEXT change; `perdecl_kill_test` asserts the cause substrings. The `(*S).M` deref-adapter refusal
  (`emitMethodExpr`) is reached only for DECLARED value methods. Decoder (`GoLean/NativeToIR.lean`): a v1 wire
  refuses by name («schema golean-native-v1 predates G-P S2 … re-export»), `wrapper` left `decodeMethod`'s allowed
  keys AND is refused by name («retired at G-P S2»), the S1 cross-check (`forwardingCalls`/`promotionRecvChain`)
  retired, every S1 record validation kept (the declared-conflict rule now reads the carrier's method table:
  `methods.any (·.funcId == methodFuncId type member)`), `promotions` required; the stub cause stored with the
  `frontend-quarantined: ` marker. `tools/lowerdiag/main.go` lists stub RECORDS as `promoted` rows (the wrapper skip
  gone). `tools/raftsubject/reachability.py`: `promoted_labels`/`promotion_target_key` — a record's display label
  resolves to its target as a graph entry (two records under one label are ambiguous, as two declarations were).
- **Controls**: `scripts/check-wire-boundary` — 12 promotion-record controls: the 9 record mutants kept, the two
  wrapper mutants (`prom-path-disagree`, `prom-wrapper-without-record`) retired, three ADDED — `prom-wire-v1` (a v1
  schema string), `prom-wrapper-key` (`wrapper` on a declared method), `prom-record-removed` (`outer.val`'s record
  deleted: the run-time dispatch refuses «dynamic type main.outer has no method val» — no wrapper stands in); the
  fixture's `probe` answers 42 through the records (`wrapI.val` re-dispatched as its own step). `Tests/GoCoreEval.lean`:
  in-process pins for the v1 and `wrapper`-key refusals; the 11 hand-built wires and `Tests/MethodIdentity.lean`'s at
  `golean-native-v2`; `Tests/unseq-wire/*.json` (140) REGENERATED by `build.py --frontend <S2 frontend>`
  (each: the schema string). `tools/method-identity-dispatch.py`: the graph control reads the two `main.Mix.m`
  records' targets; the `collide-wrappers` mutation site (`key := methodFuncKey(tName, member)`) survives in
  `promotionRecords` and rejects with the same `stuck` text. `tools/lowerdiag/unclassified-formats.txt`: the
  unclassified set is unchanged (the header's counts were already stale).
- **The twin pin** (`baselines/pins/twin-chdriver.wire.json`): 7e8c06e6… → 0b58402a…; `methods` 537 → 481 (the 53
  wrappers and 3 promoted stubs gone; every remaining entry byte-identical, same order); the 56 records UNCHANGED
  from S1; every other top-level key IDENTICAL (a key-by-key JSON comparison); the twin decodes under the v2
  decoder (probed: a nonexistent-function stuck AFTER decoding), the S1 pin is refused by name; written reason in
  `scripts/check-frontend-pins`' header. Not re-run under the machine (40–65 min).

**The race footprint (S8, decision 6 — THE documented access-trace change).** Every row whose access trace changes
is a row with a VALUE-receiver dispatch through a `*S` box whose promotion path has a `deref`/`addr` adjustment or an
embedded-POINTER hop — the shapes `dispatchLeaf` fell back to the whole pointee for (BUG-041's S3 addendum); the
footprint is now the path's cells (the pointer field, then the pointee). Measured: `scripts/diff-one` on the 8 named
rows (all PASS) and the full gate over the 3784 rows — EXACTLY ONE race verdict moved: `race/free/promoted-ptr-hop`
FAIL/confluent → PASS/confluent (|set|=1 certified over all schedules, steps 582); `race/negative/{promoted-ptr-hop-
target,promoted-ptr-hop-field,promoted-dispatch,iface-dispatch}` stay PASS/racy (steps 198/222/174/172) and
`race/free/promoted-ptr-box` PASS/confluent (steps 581). No other row of the `race/` lane or the corpus moved (the ci
result below). Removed from BUG-041's Cases: line; BUG-041's S3 addendum gained the retirement paragraph; the ledger's
Q-RACEPATH row 2 → 1 reds, the reds table Q-* 10 → 9.

**Step/fuel accounting (design §5 (ii), decision 8).** A promoted dispatch no longer runs the wrapper's frame entry,
its argument evaluation, its forwarding call and its return; a path ending in an embedded interface field costs
ONE extra step (the re-dispatch, S5) instead of the wrapper's several. No tracked record, test or baseline row
carries an exact step count over a promoted dispatch: the differential baseline records stage only,
`Tests/GoCoreEval.lean` asserts no step count on a promoted call, and the one certified record
(`baselines/certified/imported-goose__channel__google-search.certified.json`) carries an `observations_sha256` and
no step count (it is STALE by wire hash and compiled inputs — the train's 5a re-certification; a changed certified
SET there would be a finding). MEASURED instead (`.tmp/steps-compare.tsv`): the enumerator's `steps=` for every
enumerating-lane row (141 confluent/racy manifest rows), the S1 binary on the S1 wire vs the S2 binary on the S2
wire under `scripts/diff-coverage`'s parameters — 7 rows moved, ALL promoted-dispatch rows, and every other row's
count is identical: `embedding/promoted-dynamic-surface/go-nil-iface-embed` 109 → 76, `…/go-nil-ptr-embed` 115 → 70,
`race/free/promoted-ptr-box` 674 → 581, `race/negative/promoted-dispatch` 205 → 174,
`race/negative/promoted-ptr-hop-field` 255 → 222, `race/negative/promoted-ptr-hop-target` 255 → 198,
`race/free/promoted-ptr-hop` (S1: the enumeration refused at the false race; S2: 582). One row,
`goroutines/worker-pool/sum`, refused IDENTICALLY on both sides under this script's parameter reproduction
(`backEdge scheduling site of bound 2 …` — its `cases.tsv` params are not fully mirrored by the script; the gate
itself runs it green) — not a move. No pool scheduling point is lost (boundaries arise at spawns and registry ops
only): the `l1Sched`/`postOp` consumption dumps are byte-identical for every row but the un-refused
`promoted-ptr-hop`.

**Zero behaviour change — the whole-corpus choice trace** (`scripts/choice-trace-corpus --dump --jobs 6 --golean
.tmp/golean-s2 --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused --out
.tmp/ct-s2` under the lock — 3748 wires exported, the SAME 34 frontend refusals and 2 exclusions as the reference; the
S0 reference's sorted dumps/results as S1 left them, `.tmp/ct-ref-dump.sorted`, `.tmp/ct-ref-results.norm`; both runs
exit 1 «FINDINGS present», the summarizer's standing findings): every per-consumption DUMP row (`LC_ALL=C sort`ed,
`cmp`ed) and every RESULT row is BYTE-IDENTICAL to the reference EXCEPT the rows of the FOUR flipped ids and the
absolute-path row — precisely: (i) `race/free/promoted-ptr-hop`: `race` → `ok` on all 6 streams (the run no longer
refuses at the false race; the 10 dump rows the S2 run has and the reference has not are this id's pool
consultations AFTER the point where the reference refused — `l1Sched`/`postOp`/`l5ExitWindow` picks of the remaining
schedule; the reference's own consumptions up to the refusal are unchanged); (ii)
`embedding/promoted-ptr-method-expression/{promoted-value,recover}` and (iii) `noodler/frontier/
promoted-method-expression-ptr`: `unsupported` → `ok` on all 6 streams, `consumed=0` on both sides (no consumption
dump rows exist for them on either side — a method expression's call consults nothing); (iv)
`arrays/materialization-budget/over-budget`: the decoder's refusal text names its input file under the run's `--out`
directory (S1's known row). Dumps 26 367 → 26 377 rows (the 10 above), results 22 489 = 22 489 rows; the `unseqPanic`,
`nilValueMethodText`, `mapIter`, `appendSpill`, `tryLock`, `l2Entry`, `l4Waiter` consumptions of EVERY other row are
byte-identical — the `nilValueMethodText` consumption count is unchanged (S9). Nothing outside the documented items
moved.

**Detector-soundness** (`scripts/detector-soundness --out .tmp/detector-soundness-s2`, defaults `--runs 5 --procs 1,8
--jobs 6 --select in-scope`, under the lock, 2026-09-29T01:13→01:45Z): 749 in-scope rows; cells agree-DRF 605,
agree-race 43, over-refusal 6, refused 9, uncertified 86; **HOLE 0, possible-HOLE 0**; EXIT=2 = «INCOMPLETE matrix —
refused 9»: the nine refused rows are the pre-existing membership-lane `sync/{trylock/*,out-of-scope-trylock/
trylock-uncontended,promoted-mutex/trylock-expr}` whose `cases.tsv` params (`width=2,members=2`) omit `sites=` —
the runner refuses to invent a bound; not this lane's rows, unchanged by it. The 6 over-refusals are the standing
ones: `race/free/array-dyn-index-read-write` (the O1 dynamic-index residual, BUG-041, by design) and 5
`race/gomem-only/*` (BUG-084's designed divergence, refused by [USER] ruling Q-U4RESIDUAL (A)). THE S2 CHANGE:
`race/free/promoted-ptr-hop` is `agree-DRF` (gc DRF-in-5 at procs 1 and 8, machine DRF) — at S0 it sat in
over-refusal; every promoted row agrees (`race/free/promoted-ptr-box` agree-DRF, `race/negative/{promoted-dispatch,
promoted-ptr-hop-target,promoted-ptr-hop-field}` agree-race, `embedding/promoted-dynamic-surface/{go-nil-ptr-embed,
go-nil-iface-embed}` agree-DRF, `sync/promoted-mutex/{stmt,defer-unlock,value-var,counter}` and `sync/escapes/
{promoted,promoted-method-value}` agree-DRF). BUG-080's two rows (`race/negative-sync/{wg-overwrite,mutex-copy}`,
the HOLEs of the 2026-09-02 record) are agree-race today. Artifacts under `.tmp/detector-soundness-s2/`
(`summary.txt`, `matrix.tsv`); nothing written under `artifacts/` or `docs/evidence/`.

**The full gate** (`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow`, under the lock; log `.tmp/gate-s2-ci-slow.log`):
RESULT: FAIL, 1006 s wall, by exactly the expected merge-protocol 5a pair: `certificate provenance` STALE (the
reconciler's C9 names the first changed compiled input, `GoLean/CLI.lean`; the certification controls all PASS) and
the ONE drifted row `imported-goose/channel/google-search` PASS/membership → FAIL/membership (its certified record's
`wire-sha256` has been STALE since S1's `promotions` key; the wire changed bytes again at S2). The differential:
3784 rows, pass=3548 fail=236 against the re-pinned baseline 3549 / 235 — that one row is the whole difference; the
baseline-diff step names it alone; the re-pin guard: 0 PASS→non-PASS flips, the 4 GREENED rows listed (the three
predicted + the noodler re-hit); the negative corpus 394 match; every other step ok — core build WARNING-free, core
totality audit (88 required theorems present), admission proofs, declaration boundary, wire boundary, method
identity, unseq scheduler/wire, frontend pins (twin = pinned bytes), import-goose, frontend unit tests, lowering
tables, harness tests, eval tests 298 ok, lane validation, derived oracle artifacts. `baselines/certified/` untouched
here (design §4: «train step 5a re-certifies … a provenance refresh, not a claim change»). The reconciler's
report-only findings: C9 (above), C13 (pre-existing doc-site Go versions, not this lane's), C5 (this lane's FR-3
cell — fixed post-gate, §4).

**[AGENT] choices** (the design left them to the implementer): (i) the `Entry` inductive as the entry outcome and the
re-dispatch shapes above (a re-entered call position for calls; a re-queued pending call for the drains and the spawn
— no new `Cont`/`Config` constructor); (ii) the frame's `fid` = the entered function's id, last field; (iii) the stub
record's nil-first order (the retired entry's auto-deref check kept, its whole-pointee read dropped — the run refuses
either way); (iv) the declared arm keeps «target found before the receiver read» (the BUG-087 mirror), the promoted
arm walks then looks the target up (the wrapper's order); (v) the `frontend-quarantined: ` marker added by the
DECODER to a stub record's cause (the core stays marker-free); (vi) the FR-23 stub cause re-worded (truthful text over
a byte-identical results file — the one refusal-text change, attributed below); (vii) `ProgramCtx.ofTables` gained a
trailing defaulted `promotions`; (viii) `reachability.py` resolves a record label to its target (S7's reading of a
record as a callee).

### S3 — the equation lemmas and the records (no definition changed)

Design §5 S3, §3 (the exposed set) — all ten §6 decisions as recommended ([USER] 2026-09-28 relayed); PLUS the
coordinator's addition (the logic team's note of 2026-09-28, request 5, relayed by the [USER]; [AGENT] coordinator
disposition): pin `enterFrame_declared` (row 67 — CONFIRMED present and unchanged), `receiverAt_nil_path` and
`resolveMethod?_declared` in `BridgeSet.lean` and the required list; state and prove the `findFunctionIn?`
domain-narrowing bridge. No deviation from any ruled decision; no definition in `GoLean/GoCore/` changed (no
restatement was needed: every lemma is proved over the S2 definitions by `rfl`/`simp`/`cases`, no `decide`); the
`#eval`-before-`decide` rule had no occasion.

**The lemmas landed** (docstrings cite the design; `variable {ctx}` blocks beside their definitions):

- `GoLean/GoCore/Syntax.lean`, after `findFunctionIn?`: `findFunctionIn?_eq_find?` (the lookup IS `List.find?` over
  the table), **`findFunctionIn?_filter`** — exact statement
  `findFunctionIn? funcs id = some f → p f = true → findFunctionIn? (funcs.filter p) id = some f` —,
  `findFunctionIn?_filter_none` (the `none` direction), `findFunctionIn?_some` (the answer carries the id — over the
  table's `==` — and is a table row). The docstring states the migration reading: the pin's table = declared
  functions + synthesized wrappers, the post-P table = that table filtered by «declared» (the retired
  `¬ Func.wrapper`), so every declared function a client's premise names is found unchanged.
- `GoLean/GoCore/Ops.lean`, after `promotion?`: `methodDecl?_eq_find?`, **`methodDecl?_some`** (a declared method of
  exactly the dynamic type: `(info.id == member) = true ∧ (methodRecvDynamicTy? info == some dynTy) = true ∧ info ∈
  ctx.methods`), `promotion?_eq_find?`, **`promotion?_some`**. After `resolveMethod?`: **`resolveMethod?_declared`**
  (empty path, `asIs`, target `.method info.funcId`), **`resolveMethod?_ptrDeclared`** (the `*T ⊇ T` arm: `*elem`
  declares nothing for the member, `elem` neither a pointer nor an interface, `elem` declares it → empty path,
  `deref`), **`resolveMethod?_promoted`** (value box `.defined idx` named `carrier`, no declaration, record `p`,
  `p.inPtrSetOnly = false` → `some (.ofPromotion p)`) and **`resolveMethod?_promotedPtr`** (the pointer box; no
  membership premise). After `receiverAt`: `promotionHop_nil`, `promotionWalk_nil`, **`receiverAt_nil_path`**
  (`receiverAt ctx state root #[] .asIs = .ok (root, [])` — the identity), **`receiverAt_nil_path_deref`**
  (`receiverAt ctx state (.addr l) #[] .deref = Mem.load ctx state l` — the single pointee read),
  `receiverAt_nil_path_deref_nil` (the nil box: the nil-dereference panic, BUG-087 member 0),
  **`receiverAt_nil_panic`** (`path.toList = h :: hs → receiverAt ctx state .nil path adjust = .error (.panic
  nilDerefPanicText)`), **`receiverAt_field`** (`h.ptr = false → receiverAt ctx state (.addr l) #[h] .asIs = Mem.load
  ctx state (Loc.field l h.owner h.field)` — exactly the field cell's read), `receiverAt_field_proj` (from a struct
  value in hand: the projection, no read), `receiverAt_field_addr` (a pointer receiver via a value embed: the field's
  address, no read), **`receiverAt_ptr`** (`h.ptr = true`, the pointer field's `Mem.load` = `.ok (pv, tr)` →
  `.ok (pv, tr)`), `receiverAt_ptr_deref` (then the pointee: `.ok (v, tr ++ tr')` — decision 6's two loads),
  `receiverAt_ptr_nil` (a nil embedded `*E` to a pointer receiver: `.ok (.nil, tr)`, no panic — S4),
  `receiverAt_ptr_nil_deref` (a value receiver out of it: the panic).
- `GoLean/GoCore/Machine.lean`, after `Cont.rebuild_stop`: `Cont.rebuild_isSome`, `Cont.rebuild_getD_glue`; after
  `recoverResult`: `recoverAtDeferred_marker` (definitional), `recoverAtDeferred_none`, `recoverResult_frame` (the
  frame rule: `recoverAtDeferred` on the frame's tail decides), **`recoverResult_eq`** (the deferred frame directly on
  `panicResumeK chain k`: `markNewestRecovered chain` decides — payload + marked marker, or `.nil` unchanged),
  `recoverResult_frame_none`, `recoverResult_glue` (through `Cont.isGlue`: the tail's answer under the rebuilt glue).

**Names vs the design's §3** ([AGENT], the brief's «adjust names to what fits»): `resolveMethod?_promoted` is TWO
lemmas — `_promoted` (value box, with the `inPtrSetOnly` membership premise) and `_promotedPtr` (pointer box, none);
`receiverAt_nil_path` is stated as the design asked («the identity or the single deref — state both») as `_nil_path`
(identity) + `_nil_path_deref` (the read) + `_nil_path_deref_nil` (the panic); `receiverAt_field` / `receiverAt_ptr`
each come with their projection/`addr`/`deref`/nil companions so that every S4 nil point (decision 4) and both S8
load shapes (decision 6) are a stated equation; `recoverResult_eq` comes with `_frame`, `_frame_none`, `_glue`. The
design's five headline names all exist under their own names.

**[AGENT] choices**, recorded for the audit: (i) the lookup characterizations (`methodDecl?_some`, `promotion?_some`,
`findFunctionIn?_some`) are stated over the table's `==` (`(info.id == member) = true`), NOT over `=`: `FuncId` and
`Declaration.MemberId` derive `BEq` and `DecidableEq` separately and carry no `LawfulBEq` instance — no instance was
invented, the statement is the machine's own identity test; `promotion?_some`'s `p.type = carrier` IS propositional
(`TypeId` has `LawfulBEq`). (ii) The whole §3 set is PINNED (BridgeSet RE-PIN 4, rows 68–89: 22 rows, nothing
re-pinned) and REQUIRED (`Tests/GoCoreAudit.lean` 88 → 110), not only the brief's three plus the bridge: the set IS
the interface the window delivers (charter row 3, «equation-lemma style»); the supporting facts (`_eq_find?`,
`_some` of `findFunctionIn?`, `promotionHop_nil`/`promotionWalk_nil`, `recoverAtDeferred_*`,
`recoverResult_frame_none`, `Cont.rebuild_isSome`/`_getD_glue`) are unpinned but named in the changelog. (iii)
`resolveMethod?_ptrDeclared`'s pointee side condition is two negative premises (`∀ t, elem ≠ .pointer t`,
`∀ i, elem ≠ .interface i`), read straight off `resolveMethod?`'s match — no new predicate. (iv)
`receiverAt_field_proj` needs NO `h.ptr` premise (a struct value in hand is projected whatever the field's kind — the
lemma says so). (v) `Cont.rebuild_isSome` is proved by well-founded recursion on `sizeOf k` (the file's own
`Cont.sizeOf_tail_lt`), not by `Cont.rebuild.induct`.

**Records moved to the record form** (the mechanisms named as CURRENT are gone; history kept dated; no ruling or
quote rewritten): `docs/BUGS.md` — BUG-007 (Status: current mechanism = static projection chains + promotion records,
the equations by row; HISTORY paragraph = the wrapper era), BUG-015 (Status: `recoverAtDeferred`, the gc rule with
every frame a non-wrapper frame, rows 87–89; HISTORY = the marker/`recoverThroughWrappers` fix), BUG-041 (the «S3
convergence addendum» framed HISTORY; a CURRENT MECHANISM paragraph naming the footprint equations by row), BUG-087
(Status: the family test over `resolveMethod?`'s empty path with `deref`, a promoted entry outside the family; a
HISTORY bracket on the 2026-09-03 FIXED paragraph's `concreteMethodForDynamic?`/`Func.wrapper` wording);
`docs/2026-08-10_method-set-record-contract.md` §5 (the superseded bullet's `synthesizePromotionWrappers` dated, the
record consequence stated; §3 and §6 were already in the record form since S2); living design/contract notes with a
current-tense wrapper statement: `docs/2026-08-05_embedding-interfaces-design.md` (a dated ADDENDUM after the BUG-015
addendum: D1.3's dynamic mechanism deleted, D1.1/D1.2/D2 stand), `docs/2026-07-30_interfaces-campaign-design.md` (Q3
bracket: `resolveMethod?`'s three arms), `docs/2026-09-04_core-docstring-ledger.md` (the «surviving statements»
sentence), `docs/2026-09-05_e13-b-design.md` (`recoverTransparent` → the recover walk descends `Cont.isGlue`),
`docs/2026-09-04_g6-reflect-design.md` (the predicate list), `docs/2026-08-06_channels-arc-design.md` (a dated bracket
before the `wrapperForwardArg` description), `docs/language-coverage-ledger.md` FR-23 row (the emitter cell:
`promotionRecords`/`promotionStubRecord`). LEFT ALONE as dated records: the evidence bundles, the codex briefs, the
plans/reviews/audits/handoffs/logs of 2026-08-06 → 2026-09-24 that describe the wrapper era as their present
(`reasoning-surface-plan`, `master-plan*`, `grumpy-professor-review`, `hygiene-wave3-design`,
`semantics-design-audit*`, `c1-memory-module-*`, `b7-context-store-handoff`, `hygiene-slice-log`,
`roadmap-customer-alignment`, `proposal-to-logic-team`, `qrow-rulings`, the window charter/plan rows that SAY P
deletes `Func.wrapper`). Code comments (comments only, no behaviour): `GoLean/GoCore/Value.lean` (the `Ty` BEq
docstring's `concreteMethodForDynamic?`), `GoLean/GoCore/Ops.lean` (the `AccessTrace` docstring's «dispatch target's
shape (`dispatchLeaf` below)» and the O1 over-approximation paragraph's «dispatch read at `dispatchLeaf`»). The
remaining code mentions (`Ops.lean`: the `methodDecl?` and `resolveMethod?` docstrings, the path-walk section header;
`Machine.lean`: the `Cont` algebra header, the `recoverAtDeferred` docstring; `Syntax.lean`: the `Func.wrapper`
tombstone in `Func`; `StateWf.lean`: the B7 tombstone records and `recoverAtDeferred_locSup`'s docstring;
`Tests/GoCoreContract.lean`'s header; `emit.go`'s `promotionRecords` comment; `promotion_test.go`) are dated
«retired / DELETED / before G-P S2» tombstones and stay.

**Changelog** (`docs/changelog/61958f2e-WINDOW.md` row 3): the migration table gained the `findFunctionIn?` DOMAIN
row (unchanged signature; the bridge `findFunctionIn?_filter` and its companions), the «§3 equation lemmas» row
(every name, what each states), the BridgeSet row's RE-PIN 4 and the required-list counts (85 → 88 → 110); the
section header says the table is COMPLETE; the window's P line gained its S3 sentence (and names the fourth flipped
row, `noodler/frontier/promoted-method-expression-ptr`, beside the design's enumerated two).

**The gates** (S3 tree; logs `.tmp/gate-s3-*.log`, `.tmp/gates-s3-summary.log`, `.tmp/gate-s3-ci-diff.log`): the
explicit-target build `lake build GoLean GoCoreAuditTests` (58 jobs, warning-free — `Syntax.lean` is interface-hot,
so the whole library rebuilt); the individual gates and the full `ci --diff` as in the §1 row. The `ci --diff`
differential count 3548 / 236 EQUALS S2's — S3 moved no row; the two FAIL steps are the merge-protocol 5a pair
(`certificate provenance` STALE on compiled inputs; the drifted `google-search` row), exactly as at S1 and S2;
`baselines/certified/` NOT re-pinned (the train's 5a step). The `LEAN_TIMEOUT_SECONDS=1 … TIMED OUT` lines and the
`control FAILED; scratch retained` line in the log are the gate's own negative controls (the same 7 + 1 lines in
S2's log). The S3 records (this file, the changelog's landing words) were written after the runs they report; the
committed tree differs from the gated tree by these records files only (§4).

## 2. Changelog lines owed (`docs/changelog/61958f2e-WINDOW.md`)

LANDED at S3 (2026-09-29): the `findFunctionIn?` domain row, the «§3 equation lemmas» row, the BridgeSet RE-PIN 4
cell, the P line's S3 sentence — all in the row-3 section (above). Nothing owed by this lane after S3.


LANDED at S2 (2026-09-29): the row-3 section «P, native method promotion (G-P S2, the switch)» — the MIGRATION TABLE
of named replacements (`Func.wrapper`; `Cont.frame`'s last field `Bool` → `FuncId`; `enterFrame`'s `Entry`; the
delivered entry configurations; `concreteMethodForDynamic?` → `resolveMethod?`; `concreteMethodSignature?` →
`funcSignature?`/`resolvedSignature?`; `dynamicDispatch?`'s `Dispatched`; `dispatchLeaf`/`wrapperForwardArg`/
`recvFieldChain` deleted; the callee lookup → `callee?`; `Cont.recoverTransparent`/`recoverThroughWrappers` →
`recoverAtDeferred`; `Program.promotions` consumed; `ProgramCtx.ofTables`; the `Tests/MethodIdentity.lean` controls;
the wire; BridgeSet RE-PIN 3) and the window's P line. S3 adds the equation lemmas' line. The S1 lines below were
folded into that section.

Owed by S1 (drafted here at S1, [AGENT]; FOLDED into the row-3 section at S2):

- `Program.promotions : Array Promotion := #[]` ADDED (`GoLean/GoCore/Syntax.lean`, with `PromotionAdjust` /
  `PromotionHop` / `PromotionTarget` / `Promotion`; `ProgramCtx.promotions`). Data only in S1 — no machine consumer;
  `[inf]` a re-pin touches nothing: the field is defaulted and last, every structure literal spelling the other fields
  compiles unchanged (`ProgramCtx.ofTables` unchanged).
- Wire: the top-level `promotions` array is REQUIRED (schema string UNCHANGED in S1, `golean-native-v1`; the v2 move —
  wrappers retired, `"wrapper"` refused — is S2); a wire without it refuses by name (`program.promotions is missing`);
  every record is validated (`NativeToIR.lean` `validatePromotion`) and cross-checked against its wrapper/stub (the S1
  cross-check RETIRES with the wrappers at S2).
- Decoder refusals ADDED (each names the record `program.promotions[i] (<type>.<member>)` and the fact): missing
  field; unknown key; `adjust` outside `asIs|deref|addr`; `target` not exactly one of `method|iface`; `unsupported`
  without `sig` / `sig` without `unsupported`; carrier not a struct on the wire; empty path; hop owner ≠ the reached
  type; owner imported/opaque or not a struct; no such field; not an embedded field; `ptr` vs the field's type;
  intermediate hop reaching a non-struct; target method absent (unless the imported-unexported rule above holds and the
  key is derived from the reached type and member); member identity ≠ the target's; target an interface anchor; last hop
  ≠ the target's receiver base; target itself a wrapper; interface target ≠ the reached interface / undeclared / not
  declaring the member; `inPtrSetOnly` ≠ spec#Struct_types' rule; `adjust` ≠ the required one; `sig.id` ≠ member;
  duplicate `(type, member)`; the carrier lacks the method; receiver kind ≠ `inPtrSetOnly`; `(type, member)` a DECLARED
  method; wrapper callee ≠ target; wrapper receiver chain ≠ the record's; argument count; stub cause ≠ the record's;
  stub signature ≠ `sig`; a wrapper without a record.
- Twin pin `baselines/pins/twin-chdriver.wire.json`: 1c4e7038… → 7e8c06e6… (56 records; `check-frontend-pins` header).
- `scripts/check-wire-boundary`: +12 promotion-record controls (fixture `Tests/wire-boundary-promotion/`).

## 3. PENDING [USER] items

**None posed at S0, S1, S2 or S3.** Every ruled decision (design §6, 1–10) was followed as recommended; the
coordinator's two [USER]-ruled additions (the frame's `FuncId` field, S2; the pins + the `findFunctionIn?` bridge, S3)
are DONE where quoted. What the lane leaves for the [USER] is the merge sign-off after the audit — nothing else.
[AGENT] readings the audit should see, none a deviation: S1 — the ONE acceptance rule beyond the design's letter for a
record whose `method` target has no declaration on the wire (accepted iff the reached type is imported/opaque and the
key is exactly `methodFuncId reached member`; the call then refuses by name — the twin's `raft.DefaultLogger.output`);
S2 — choices (i)–(viii) in §1 S2 (the `Entry` shapes; the frame's `fid` = the entered function, and the anchor for the
spawn's re-dispatch barrier; the stub record's nil-first order; the declared arm's «target before receiver» order;
the decoder-added `frontend-quarantined: ` marker; the FR-23 cause re-wording; `ProgramCtx.ofTables`' trailing
default; `reachability.py`'s label resolution), and the fourth flipped row
`noodler/frontier/promoted-method-expression-ptr` — the `(*T).M`-over-promoted class the design's §5 did not enumerate,
attributed to decision 5; S3 — choices (i)–(v) in §1 S3 (the `==`-form characterizations; pinning the whole set; the
side-condition form; the premise-free projection lemma; the WF proof).

**Audit ask (for the coordinator — the pre-merge adversarial audit is owed, never skipped; scope and waiver are the
[USER]'s).** Suggested scope: aim it at the design's §2 claims and the ZERO-BEHAVIOUR-CHANGE criterion (§5), not at
the gate. Look hardest at: (1) the [AGENT] choices logged in S1 and S2 (§1 S1 «one rule beyond the design's letter»;
§1 S2 choices (i)–(viii)); (2) the one acceptance rule for absent imported targets — that its refusal-by-name at the
call is the only observable consequence and that no locally declared type can slip through it; (3)
`noodler/frontier/promoted-method-expression-ptr`'s flip OUTSIDE the design's enumerated list (decision-5 class) — that
its new PASS is a right answer, not a coincidence of the deref adapter's retirement; (4) the spawn re-dispatch
barrier frame's `fid` (the anchor, not a body-bearing function) — whether a client observing «f returned v» at that
frame's exit is misled; (5) the FR-23 stub cause text (choice vi) — that the re-worded cause is truthful for every
FR-23 shape and the results file stayed byte-identical; (6) the S2 stub-order choice (iii): the retired entry's
nil-first auto-deref check kept, its whole-pointee READ dropped — that dropping the read changes no race verdict (the
run refuses either way, but the access trace before the refusal is shorter); (7) S3's equation statements against
the S2 definitions — that each lemma says what its docstring claims (in particular `receiverAt_nil_path_deref` = the
WHOLE pointee, `receiverAt_field` = ONLY the field cell), and that pinning them does not restate any definition.

## 4. Operational notes

- Warmed `.lake` from the primary checkout's `.lake/build` (lake rebuilt only the stale modules; `lake build golean` 106 jobs).
- The box-wide lock is taken by `.tmp/locked-gate.sh` (atomic `mkdir`, owner file, trap release, 120 s wait-retry).
- Post-gate edit disclosed: after the S0 gate the reconciler's report-only C5 finding named the ledger's FR-3 cell (a lane name
  in backticks read as a case citation); the backticks were removed — a records-only one-token change, reconciler re-run clean
  of C5; not re-gated.
- `TMPDIR=.tmp` for every harness run (the coverage scripts `mktemp` under `$TMPDIR`).
- S1 ([AGENT] sub-worker): `Syntax.lean` is interface-hot — the explicit-target `lake build golean` rebuilt 106 jobs
  (≈ 8 min under `GOLEAN_MEM_MAX=40G LEAN_NUM_THREADS=6`), lock-exempt; the decoder-only rebuild ≈ 2 min. The
  individual gates ran sequentially from one script (`.tmp/run-gates.sh`, per-gate logs `.tmp/gate-*.log`, each judged
  by its captured exit code). The S1 choice trace: `.tmp/locked-gate.sh .tmp/ct-s1.log env GOLEAN_MEM_MAX=48G
  scripts/capped scripts/choice-trace-corpus --dump --jobs 6 --golean .tmp/golean-s1 --exclude … --out .tmp/ct-s1`
  (the binary COPIED to `.tmp/golean-s1` so later rebuilds cannot disturb the run); export ≈ 8 min, tracing ≈ 3 min. The
  reference run itself exits 1 («FINDINGS present» — the summarizer's standing findings, identical on both sides); the
  zero-change evidence is the BYTE identity of the sorted dumps and results, not the exit code.
- The record census over the exported wires (counts in §1 S1) was an ad-hoc Python pass over `.tmp/ct-s1/wire` against
  `.tmp/ct-ref/wire` (every top-level key compared; not tracked — re-derivable from the two exports).
- Post-gate edit disclosed (S1): the S1 row's gate/trace RESULT lines and this note were written after the runs they
  report; the committed tree differs from the `ci --slow`-gated tree by this records file only.
- S2 ([AGENT] sub-worker, 2026-09-28/29): interface-hot edits (`Syntax.lean`, `Ops.lean`, `Machine.lean`) were warmed
  SEQUENTIALLY by explicit targets (`lake build GoLean.GoCore.Ops`, then `…Machine` ≈ 3 min, then `…StateWf` ≈ 1 min per
  attempt, then the proof modules in one background `lake build` of named targets), all under
  `GOLEAN_MEM_MAX=40G LEAN_NUM_THREADS=6 scripts/capped`, lock-exempt; the three heaviest proofs
  (`dynamicDispatch?_locSup`, `promotedCallee_locSup`, `enterFrame_wf`; `enterFrame_declared`) were developed in scratch
  files under `.tmp/scratch/` against the built `.olean`s (`scripts/capped lake env lean <file>`, ≈ 20 s a turn) with the
  StateWf statements temporarily stubbed `sorry` — the stubs were replaced before any full build, and the final build is
  `sorry`-free and warning-free (`.tmp/build-s2-full3.log`). `StepErrors.lean` is the slow module (`stepFn_strict`,
  ≈ 5–6 min per elaboration) — an `errp` leaf for the new structural recursion (`promotionWalk_tame`) was the one addition
  it needed. Macro hygiene lesson: an `rcases`/`obtain` `rfl` pattern inside a `macro` quotation is a hygienic name, not
  the `rfl` pattern — it BINDS a hypothesis named `rfl✝` and substitutes nothing (the existing `entryV_arm` macros use
  `obtain ⟨h1, …⟩ … subst h1` for that reason; `enterFrame_run_arm`/`enterFrame_again_arm` do too).
- The whole-corpus choice trace ran under the lock (`.tmp/locked-gate.sh .tmp/ct-s2.log …`, the binary COPIED to
  `.tmp/golean-s2`; export ≈ 8 min, tracing ≈ 3 min); the individual gates ran sequentially from `.tmp/run-gates-s2.sh`
  (per-gate logs `.tmp/gate-s2-*.log`, exit codes in `.tmp/gates-s2-summary.log`), concurrently with the trace (they are
  lock-exempt). A FIRST `ci --slow` was started before the trace's diff had been read; the trace showed the fourth flip
  (`noodler/frontier/promoted-method-expression-ptr`), so that run was stopped by its own process group (`kill -TERM --
  -<pgid>` — PIDs only, never a pattern; the lock's owner file was checked released) ≈ 3 min in, the row was re-pinned
  with its reason, and the gate was restarted; only the restarted run is reported.
- Post-gate edit disclosed (S2): after the `ci --slow` run the reconciler's report-only C5 named the ledger's FR-3 cell
  (a backticked doc path read as a case citation — S0's lesson again); the backticks were removed — a records-only
  one-token change, reconciler re-run clean of C5; not re-gated. The S2 row's RESULT lines and this note were written
  after the runs they report; the committed tree differs from the gated tree by the records files only (this handoff,
  the ledger cell, the changelog's landing words).
- `git status` at the S2 tree: 44 tracked files edited + the 140 regenerated `Tests/unseq-wire/*.json`; no new tracked
  file. The box's `app.slice` holds ≈ 2 800 leftover `capped-*` cgroup directories (box-wide litter, not this lane's to
  clean; noted for `docs/operational-lessons.md`'s owner).
- S3 ([AGENT] sub-worker, 2026-09-29): every lemma was developed in ONE scratch file against the built S2 `.olean`s
  (`.tmp/scratch/s3lemmas.lean`, `scripts/capped lake env lean`, ≈ 20 s a turn; four turns to a clean exit 0), then
  pasted beside its definition; `lake build GoLean.GoCore.Machine` (12 jobs) then `lake build GoLean GoCoreAuditTests`
  (58 jobs, `Syntax.lean` being interface-hot), both under `GOLEAN_MEM_MAX=40G LEAN_NUM_THREADS=6 scripts/capped`,
  lock-exempt, both warning-free. Lessons: a `match` inside a `theorem` statement elaborates to its OWN matcher constant,
  so `rw` with a fold-characterization lemma fails to find the pattern while `exact` (defeq) succeeds — the `_foldl_aux`
  lemmas are applied by `exact`; `simp` (default set) rewrites `&&` to `∧` INSIDE the fold's lambda and breaks the
  induction — use `simp only [Bool.false_eq_true, ↓reduceIte]` after `cases hm : (…)` (the `cases` already substitutes
  the scrutinee, so `hm` itself is unused); a `decreasing_by` cannot see a `rename_i` name — `(by assumption)` finds the
  tail hypothesis; `Cont.rebuild.induct`'s explicit arguments are `descend` and `motive` (`act` is inferred), which is
  why the WF form was used instead. The individual gates ran from `.tmp/run-gates-s3.sh` (per-gate logs, exit codes in
  `.tmp/gates-s3-summary.log`); the first `go test` attempt failed in 0 s for want of `GO111MODULE=off` (the script
  ran it bare; the go code is untouched by S3) and was re-run in ci's environment — both lines are in the summary log.
  The full gate ran under the lock (`.tmp/locked-gate.sh .tmp/gate-s3-ci-diff.log env GOLEAN_MEM_MAX=48G scripts/capped
  scripts/ci --diff`, 1035 s); no tracked file was edited while it read the tree. Post-gate edit disclosed: this
  handoff's S3 row/section and §2/§3 were written after the runs they report (records only).
