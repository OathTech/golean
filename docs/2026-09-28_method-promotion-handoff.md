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
| S2 the switch | — | — | — | — |
| S3 equations + records | — | — | — | — |

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

## 2. Changelog lines owed (`docs/changelog/61958f2e-WINDOW.md`)

None at S0 (no code). The migration table and the S2/S3 entries land with S2/S3. Owed by S1 (drafted here, [AGENT];
to be landed in the changelog's P row with S2 — S1 alone changes no exposed semantics):

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

None posed so far.

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
