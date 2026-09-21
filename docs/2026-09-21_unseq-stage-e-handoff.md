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
| `7f7e6b79` | **E4** conversions (pure ops), allocations (`allocate` bodies without E1 edges; `make`/`new` E1 participants) — BUG-102 FIXED | EXIT=1 in 1015 s; 3728 = 3493 / 235; red = the 5a pair only | 5 flips (BUG-102's designed reds: 4 membership + `slice-lit-payload-vs-recv` strict), 4 lane moves strict → membership (`bytes-conv-value-vs-mutating-call` — E12's recorded exception retires; `noodler/latitude/{slice-literal-index-vs-call,struct-literal-var-vs-call,conversion-index-vs-call}`), 6 born (`evalorder/unseq-conv-alloc`); the FR-28 frontier row retires to 0 reds |

The 5a-class pair, identical at every gate: `certificate provenance` STALE for the changed core inputs (E1:
NativeToIR.lean; E2: Machine.lean; E3: AdmissionIndices.lean and the other core modules) and the ONE drift line
`imported-goose/channel/google-search PASS/membership → FAIL/membership` (its fresh re-certification «unchanged set»
every time — the train installs the candidate at step 5a). Whole-corpus choice traces vs main `14006270`'s binary:
E1, E2, E3 and E4 recorded in the README (the DIFFER set = exactly the rows whose sweeps the families admitted; every
other id byte-identical); E4's: §4 below.

Bug status: **BUG-113 fixed** (E1). **BUG-104 fixed** (E2 + E3; LEFT the inventory's known-≠-oracle list). **BUG-102
fixed** (E4 — its five designed reds lower and PASS; the ledger's FR-28 frontier row retires to 0 reds; E12's recorded
exception `bytes-conv-value-vs-mutating-call` retires into a membership set). **BUG-112** carries the Stage C / E2
fixed rows.

Twin (the raft twin assembly): 10 203 sweeps, **0 admitted** at every family; `scripts/check-frontend-pins` byte-identical.

Legacy census (E6's condition — ZERO legacy `unseq-probe` emissions — is NOT met): the classifier census at E4
(`census-e4.txt`) admits 127 of 108 074 corpus sweeps; the choice-trace site census still shows `unseqPanic` sites
(E2's trace: 288 → 246; E3's: 228; E4's: §4). The legacy triple (`Stmt.unseqProbe` / `Cont.probeK` /
`ChoiceSite.unseqPanic`) stays until E5 migrates the remaining probe emitters by name: multi-target / tuple forms and
comma-ok receives/assertions, map literals, array types and literals, `&x` of a variable, float/complex types,
defined non-struct types, interface-keyed / defined-key map compounds, string indexing/slicing, interface
conversions, method values/expressions, promoted fields/methods, variadic and non-main callees (the latter OUTSIDE
the grammar by design — the shim helpers are never probed). The residue counts by former reason are in
`census-e4.txt`.

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
5. **E3/E4 retirement + late structural allocations** (v2.1 §5 item 4) — REALIZED at E4: a composite literal is a
   node without E1 edges (its payload reads unordered against the sibling calls / receives — BUG-102's rows and
   the four moved rows), with the [AGENT] CORRECTION that `make`/`new` are E1 participants (function calls,
   spec#Built-in_functions; the born control `make-len-vs-call` pins it against gc, 6 on 20/20). Ratification of
   both posed at the merge ask (design §E4).
6. **The `allocate` body kind** ([AGENT], design §E4): ONE constructor over `AllocSpec` (the frontend's five hoist
   shapes) rather than a general `exec` statement body — alternative named there.

## 3. Next families (the plan of record, design §0)

**E4 conversions + allocations — LANDED** (`7f7e6b79`, design §E4). The sketch below was the plan at the E3
park; what landed differs in one point: `make`/`new` are E1 participants (the control's gc draw decided it), so a
payload read inside a `make` operand is forced before every later event and the E13 make rows
(`assert-left-make-slice`, `tgt-assert-vs-make`) stay on the legacy probe path (no effectful event beside the
assertion). Kept for the record:
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

**E5 multi-target / residue** (NEXT — not started): tuple / multi-value assignment (`a, b = f(), x`), the comma-ok
forms (`v, ok := <-ch`, `v, ok := m[k]`, `v, ok := x.(T)`), blank targets, `&x` of a variable as an operand, map
literals (an allocation whose dynamic entries gc evaluates at the literal's position — a `mapLit` `AllocSpec` arm
with the E13 guard's measured note), array types/literals (a type-grammar widening: fixed-size arrays with the
machine's `arrayLit`), string indexing/slicing (`runeAt`/`slice` on strings), interface conversions (`to-interface`
heads), method values/expressions, defined non-struct types (the `conversion` residue's largest part), float/complex
types; the census residue counted by former reason at each step. E5 also decides E3/E4 (the inventory's inter-target
order entries): a multi-target form's targets are phase-1 siblings — the natural graph shape once tuple assignment
enters. **E6** retire the legacy triple (`Stmt.unseqProbe` / `Cont.probeK` / `ChoiceSite.unseqPanic`) ONLY when the
census shows ZERO legacy `unseq-probe` emissions across corpus AND twin — after E4 the trace still records 
`unseqPanic` consumptions (§4), so E6 is NOT reachable yet; the handoff states the emitters by name above.

## 4. Whole-corpus choice traces (main vs E3, main vs E4)

`docs/evidence/2026-09-21_unseq-stage-e/choice-trace-main-vs-e3.txt`: 3686 ids — 3626 byte-identical, 43 DIFFER (exactly
the rows of the 43 packages whose sweep decisions changed main → E3), 17 only on the E3 side (the born rows); the 94
sweeps returned to legacy at E3 are SAME (no consumption on either path). Site census `unseqNext` 555 → 1288,
`unseqPanic` 288 → 228 — the legacy `unseqPanic` probe is still consulted on 228 recorded consumptions across the
corpus (E6's condition is not met; the probe emitters left are E4's conversions/allocations and E5's residue).

E4: `choice-trace-main-vs-e4.txt`: ids=3692	same=3613	differ=56	onlyA=0	onlyB=23 — the DIFFER ids exactly the rows of the 40 packages whose sweep decisions changed main → E4, the ONLY_B ids the born rows; site census `unseqNext` 555 → 1436, `unseqPanic` 288 → 204 — the legacy probe is still consulted on 204 recorded consumptions (E6 NOT reachable; the emitters by name in §1).

## 5. Operational notes for the next session

- E4's scratch: `.tmp/e4/edit-*.py` + `rename-alloc.py` (every edit as a replayable script — the rename runs AFTER
  the others), `.tmp/e4/apply.sh` (the frontend half; NOT idempotent — the edits assert their anchors once),
  `.tmp/gc-e4/`, `.tmp/gate-e4.sh`, `.tmp/nativefrontend-e4`, `.tmp/golean-e4`.
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
