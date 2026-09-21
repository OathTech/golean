# Stage E of the evaluation-order model v2.1 — lane handoff (`core/unseq-stage-e-0921`)

[AGENT] worker, 2026-09-21. Worktree `.claude/worktrees/unseq-stage-e`, branch `core/unseq-stage-e-0921`, based on
main `14006270` (the r45 train's records tip over `74d084ad`). Brief: `docs/2026-09-16_evaluation-order-model-v2.md`
§7 row E; the family plan and every [AGENT] choice: `docs/2026-09-21_unseq-stage-e-design.md`; evidence
`docs/evidence/2026-09-21_unseq-stage-e/`. NOT merged, NOT pushed. Every runtime commit below is GATED (the full
`scripts/capped scripts/ci --slow` under the box-wide lock, red on EXACTLY the two 5a-class items and nothing else).

## 1. State at park

| commit | family | gate (`ci --slow`, K=80) | rows |
|---|---|---|---|
| `0fe7bdce` | **E1** package-level variables (closes BUG-113) | EXIT=1 in 1083 s; 3709 = 3465 / 244 pinned; red = the 5a pair only | 2 flips FAIL → PASS (BUG-113), 4 born (`evalorder/unseq-globals`) |
| `6960697f` | **E2** pointers, fields, maps (BUG-104's map row → BUG-112) | EXIT=1 in 1018 s; 3717 = 3474 / 243 | 1 flip, 5 lane moves strict → membership, 8 born (`evalorder/unseq-ptr-field-map`) |
| `c1c27f27` | **E3** receives, method calls; the OBSERVABILITY trigger (BUG-104 FIXED) | EXIT=1 in 1021 s; 3722 = 3482 / 240 | 3 flips (BUG-104's last rows), `receiver-vs-arg-call` → membership, `nil-receiver-recursion` → confluent engine=dedup, `two-workers-own-chans` engine DFS → dedup, 5 born (`evalorder/unseq-recv-method`) |

The 5a-class pair, identical at every gate: `certificate provenance` STALE for the changed core inputs (E1:
NativeToIR.lean; E2: Machine.lean; E3: AdmissionIndices.lean and the other core modules) and the ONE drift line
`imported-goose/channel/google-search PASS/membership → FAIL/membership` (its fresh re-certification «unchanged set»
every time — the train installs the candidate at step 5a). Whole-corpus choice traces vs main `14006270`'s binary:
E1 and E2 recorded in the README (the DIFFER set = exactly the rows whose sweeps the family admitted; every other id
byte-identical); E3's: §4 below.

Bug status: **BUG-113 fixed** (E1). **BUG-104 fixed** (E2 + E3; LEFT the inventory's known-≠-oracle list). **BUG-102
open** — its five designed reds (`builtins/e13-sibling-panic-order/{composite-ptr-payload-vs-call,
slice-lit-payload-vs-call,composite-ptr-payload-vs-call-printroot,slice-lit-payload-vs-call-sinkroot,
slice-lit-payload-vs-recv}`) are E4's. **BUG-112** carries the Stage C / E2 fixed rows.

Twin (the raft twin assembly): 10 203 sweeps, **0 admitted** at every family; `scripts/check-frontend-pins` byte-identical.

Legacy census (E6's condition — ZERO legacy `unseq-probe` emissions — is NOT met): the classifier census at E3
(`census-e3.txt`) admits 110 of 108 045 corpus sweeps; the choice-trace site census still shows `unseqPanic` sites
(E2's trace: 288 → 246; E3's: §4). The legacy triple (`Stmt.unseqProbe` / `Cont.probeK` / `ChoiceSite.unseqPanic`)
stays until E4/E5 migrate the remaining probe emitters (conversions, allocations, multi-target forms, the interface-
keyed / defined-key map compounds, non-main callees are OUTSIDE the grammar by design and never probed).

## 2. PENDING [USER] (ratifications posed at the merge ask — none self-adjudicated)

1. **E2/E12 VALUE axis (b) → (a)** on the named rows: E1 `evalorder/unseq-globals/{read-vs-call,compound-vs-call}`;
   E2 `noodler/latitude/deref-vs-call`, `noodler/maps/compound-call-{mutates,deletes}`,
   `pointers/deref-target-rhs-call-order`, `builtins/len-vs-call-order/len-nil-only-none`, the born
   `evalorder/unseq-ptr-field-map/*` membership rows; E3 `evalorder/unseq-recv-method/{recv-vs-read,
   ptr-recv-vs-field-read}`. (Inventory E2/E12 bullets + §10.1; the pilot's precedent.)
2. **E14 receiver sub-axis (a) ENVELOPED** on `noodler/latitude/receiver-vs-arg-call` {6, 105} and the born
   `evalorder/unseq-recv-method/value-recv-vs-arg-call` {6, 15} (inventory E14 bullet).
3. **The OBSERVABILITY trigger** ([AGENT], design §E3): a sweep enters the graph iff some occurrence is unordered
   against an EFFECTFUL event; 94 all-forced sweeps returned to the legacy path with their observations unchanged.
   Alternative named: the coarse trigger (admit the forced receives; re-enumerate 403 concurrency rows for identical
   sets).
4. **Lane moves via route α** (Stage D's amended caption «all choice streams the row consumes»):
   `noodler/methods/nil-receiver-recursion` strict → confluent `engine=dedup`; `goroutines/fork-join/two-workers-own-
   chans` engine DFS → dedup. Alternatives named on the rows (`depth=N`; a raised DFS work cap).
5. **E3/E4 retirement + allocation-payload reclassification** (v2.1 §5 item 4) — E4's, not yet posed.

## 3. Next families (the plan of record, design §0)

**E4 conversions + allocations** (closes BUG-102's five reds; retires E12's recorded exception
`bytes-conv-value-vs-mutating-call`). Design sketch worked out at park, NOT started in code:
- Conversions are `Expr.convert ty e` in the core (an op; `convertValueToTy`) — an `eval` head `convert`
  (keys `target`, `x` an atom) — decoder D8 + classifier arm in `unseqExpr`'s CallExpr case (`tv.IsType()`, today's
  refusal «conversion», 5719 census rows); NO machine change. Type grammar: `unseqTypeOK` admits only
  integer/bool/string basics — `[]byte(s)` needs `uint8` (an integer: admitted) so the byte rows enter as-is;
  floats stay outside (E5's statement).
- A VALUE struct literal `T{…}` is `Expr.structLit` — an `eval` head `struct-lit` over atoms (decoder only).
- `&T{…}` is emitted as a hoisted `new` STATEMENT (`Stmt.allocNew target value typ`) with the struct-lit value;
  slice literals as `slice-lit` (makeSlice + element assigns); `make` as `make-slice`/`make-map`/`make-chan` —
  STATEMENT-bodied. Smallest machine change: ONE constructor `UnseqBody.alloc (bind : String) (spec : AllocSpec)`
  with `inductive AllocSpec | new (value : Expr) (typ : Ty) | makeSlice (elem : Ty) (len : Expr) (cap : Option
  Expr) | makeMap … | makeChan … | sliceLit (elem : Ty) (len : Nat) (elems : List (Int × Expr))` (Expr/Ty payloads
  only — no `Stmt` nesting inside `UnseqBody`, which would make Stmt/UnseqBody a nested-inductive cycle),
  `allocStmt bind spec : Stmt` mirroring `unseqRecvStmt`, two Step rules `unseqRunAlloc`/`unseqAllocDone` copying
  the recv arms in Machine/StepFn/StateWf/MachineSound/UnseqSound/SyntaxEqb/AdmissionIndices; `mentions` =
  the spec's exprs' names. An allocation carries NO E1 edges (v2.1 R3); its payload reads are the occurrences
  (`(&T{x: s[i]}).x + wit(5)` → {panic alone, `wit 5` · panic}; gc's second member inside).
- References first (enumerate.py E4a conversion / E4b allocation cases), then wires (`e4conv`, `e4alloc`), then
  the lowering; census BEFORE/AFTER; `scripts/diff-one` on the affected rows (BUG-102's five, the E13 conv/make
  rows `conv-left-call`, `bytes-conv-{left-len-hoist,payload-vs-call,value-vs-mutating-call}`,
  `assert-left-make-slice`, `tgt-assert-vs-make`, and every package whose sweeps enter); baseline re-pin; records
  (BUG-102 → fixed, inventory E12 exception retired, ledger §8ad); gate; trace.

**E5 multi-target / residue** (tuple assignment, comma-ok forms incl. the comma-ok receive, blank targets;
interface-keyed and defined-key map compounds; float types; the census residue stated). **E6** retire the legacy
triple only when the census shows ZERO legacy `unseq-probe` emissions across corpus AND twin — E4/E5 decide whether
that is reachable; if not, the handoff states why by name.

## 4. E3 whole-corpus choice trace (main vs E3)

`docs/evidence/2026-09-21_unseq-stage-e/choice-trace-main-vs-e3.txt`: 3686 ids — 3626 byte-identical, 43 DIFFER (exactly
the rows of the 43 packages whose sweep decisions changed main → E3), 17 only on the E3 side (the born rows); the 94
sweeps returned to legacy at E3 are SAME (no consumption on either path). Site census `unseqNext` 555 → 1288,
`unseqPanic` 288 → 228 — the legacy `unseqPanic` probe is still consulted on 228 recorded consumptions across the
corpus (E6's condition is not met; the probe emitters left are E4's conversions/allocations and E5's residue).

## 5. Operational notes for the next session

- Scratch (all under the worktree's `.tmp/`, gitignored): `.tmp/census/{run.sh,summarize.py,diff.py}` (the census;
  `run.sh <frontend-binary> <out.tsv>` over every `cases.tsv` dir + the twin assembly; 23 s), `.tmp/trace-compare.py`
  (Stage D's per-id byte-identity), `.tmp/main-tree-full/.tmp/trace` (main `14006270`'s dump — reuse; the main
  export tree has `deps` symlinked), `.tmp/golean-{main,e1,e2,e3}` (the binaries; sha256 prefixes 0681abc6 /
  … / 7920d88e / c8249420), `.tmp/e{2,3}/edit-*.py` (every edit as a replayable script; `apply.sh`),
  `.tmp/gate-e{1,2,3}.sh` (the lock protocol: atomic `mkdir artifacts/build-lock.d` at the primary root, owner
  file, trap-protected release, wait-retry 120 s), `.tmp/gc-e{1,2,3}/` (gc draw drivers: a copy of the package
  with `func main` renamed + `driver.go` printing the subject; `go build` per flag set, 5 runs × GOMAXPROCS 1/8
  × default / `-N -l`).
- `scripts/choice-trace-corpus --out` must be RELATIVE to the tree root; run it from the tree whose frontend
  should emit the wires (`git archive <commit>` + `ln -s` the primary's `deps` for main's side).
- The strict lane refuses by name when a row's default stream serves wide picks past the three fixed streams
  (`wide=`/`exhausted=` in the detail) — route to `lane=confluent engine=dedup` where the set is a singleton (route
  α) or declare `depth=N`; the DFS confluent enumerator's work-cap refusal → `engine=dedup` first, a raised cap
  second. The membership enumerator refutes wrong `width`/`sites` params by name — correct the params, record it.
- The decoder's D9 argument rule: an `invoke` argument may be an atom OR a `ref`/`globaladdr` (an address, never
  a read) — E3's born rows found the gap; a hand-built wire's `build.py` splice keeps the setup through the statement
  declaring `until_decl`.
- Never edit the tree while a gate or a trace reads it; the lock owner's pid can be stale while the train is live —
  wait, do not take over.
