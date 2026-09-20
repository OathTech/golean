# Adversarial audit — Stage C, the native `unseq` pilot (candidate `2dac6a75`, branch `core/unseq-stage-c-0919`, over main `6a7beb3d`)

**VERDICT (2026-09-20, at the audited tip `2dac6a75`): FIX-FIRST** — REVISED to **MERGE-CLEAN** at the fix round `6886fe00`, see the «Re-verification» section at the end.

**Original verdict line:** FIX-FIRST — MERGE-CLEAN on the semantics of every graph the frontend emits (every enumerated set is spec-permitted and contains gc's draw; every pre-existing strict row's default tape is unchanged and gc's; the legacy path is byte-identical outside the pilot; the census, the baseline, the twin and the gate reproductions all hold), with three items to fix before the merge: (F1) a pre-existing WRONG-ANSWER on the LEGACY path that the candidate's own `r2b` row exposes and that is not rowed (a binary logical operation beside a later call is evaluated after the call — spec-forbidden, ≠ gc — for every non-pilot operand); (F2) a frontend-emits/decoder-refuses REGRESSION on legal pilot-grammar Go (a constant copied into a cell: `x := true && f()`, `a[f()] = 5`, `a[f()] = "s"` ran on main and now refuse by name); (F3) the decoder's D12 (static G) is weaker than its spec letter for NESTED guard completions (the machine catches it dynamically — fail-closed, but the spec claims a static refusal). Records: one unsupported K=80 claim (F4). Nothing FAIL-OPEN was found; no member of any set is forbidden by the spec; no strict row's default tape differs from gc.

[AGENT] auditor (Claude, Fable 5.1), ordered by [USER] Mike 2026-09-20 «Great, launch the audit» (verbatim, relayed by the [AGENT] coordinator — cited as relayed). Worktree `.claude/worktrees/audit-unseq-stage-c`, branch `review/unseq-stage-c-0919` at the candidate tip; no edit to the candidate or to `main`; no push. Warm build copied from the candidate worktree at identical source (`scripts/capped lake build` → `Build completed successfully (96 jobs)`, EXIT=0). Binaries: the candidate's `golean` built here; main's `golean` `/home/dev/projects/golean/.lake/build/bin/golean` (sha256 `a014183b…`, read-only); the candidate's frontend `go build ./tools/nativefrontend`; main's frontend from `git archive 6a7beb3d tools/nativefrontend`. Oracle `go1.26.5 linux/amd64`. Evidence: `docs/evidence/2026-09-20_unseq-stage-c-audit/` (13 files, 72 KiB; `check-evidence-size` PASS). Every number below is copied from a file there or from a command whose exit code was captured.

## 1. Findings, by severity

### F1 — WRONG-ANSWER (pre-existing, LEGACY path; exposed by the candidate; un-rowed) — a binary logical operation beside a lexically later call is evaluated AFTER the call

- **What I did.** The default-tape comparison over every row of the pilot's 25 packages (main's binary + main's frontend vs the candidate's; `default-tape-comparison.txt`) found 3 differing rows: the two designed fixes and the born strict row `evalorder/unseq-pilot/r2b` (`sinkL(left || b, change())`, `change` sets `b`): MAIN `logical true 0`, CANDIDATE `logical false 0`. I then wrote the same sweep with a NON-pilot operand — `left` a package-level variable — so both frontends take the legacy path (`legacy-logical-op-vs-call.txt`, `c01`): the two frontends emit byte-identical wires; both binaries answer `logical true 0`; `go run` and `go run -gcflags=all='-N -l'` answer `logical false 0`. The `&&` variant (`c02-and`) is wrong the same way; the call-first control `sinkL(change(), left || b)` matches gc. Main's legacy wire (`r2b`, main frontend) shows the mechanism: `$c17 := change()` hoisted BEFORE the statement, `left || b` left inline in the residual.
- **Why it matters.** spec#Order_of_evaluation: «all function calls, method calls, receive operations, and binary logical operations are evaluated in lexical left-to-right order» — `left || b` is lexically before `change()`, so `false` is the ONLY permitted result; the inventory's own E12 text names this hard constraint («calls/receives/binary-logical stay lexically ordered among themselves», `docs/2026-08-11_latitude-inventory.md` ~l.1406). Observed (gc) ∉ modeled on the legacy path — a wrong answer of the same class the pilot was built to retire (v2.1 review R2/R2b: «E1 anchored at guard ENTRY (refuted)»). The candidate FIXES it for pilot operands (`r2b` born strict = gc) and changes NOTHING outside the pilot (the 0-outside claim holds — I reproduced it, §2.h), but the C3 choice-trace analysis lists `r2b` among «the 13 born rows» that differ from main without saying what the difference IS: main's legacy default is a spec-forbidden member. No BUGS.md entry covers this shape (BUG-062 is `len`/`cap`); no corpus row is red for it.
- **Where.** `tools/nativefrontend/emit.go` (the legacy ANF hoist; unchanged by the candidate); the record gap in `docs/2026-09-19_unseq-stage-c-handoff.md` §4 and `docs/evidence/2026-09-19_unseq-stage-c/README.md` §C3.
- **Proposed disposition.** FIX-FIRST, records-class for THIS candidate (it introduces no wrong answer and removes one): file a BUGS.md entry (WRONG-ANSWER class, Status open, Pinned-by differential) with a red corpus row on the legacy shape (`sinkL(g || b, change())`, `g` a package var, expected `logical false 0`), name it in the handoff §4 / README §C3 as the meaning of `r2b`'s main-vs-C2 difference, and put the fix on Stage E's list (the guard protocol for every operand family — or an interim legacy fix that anchors `&&`/`||` before later hoisted calls). «Every detected gap is rowed» ([USER] 2026-09-03).

### F2 — COHERENCE-GAP with a coverage REGRESSION (fail-closed) — the frontend copies a CONSTANT into a cell; the decoder's D8 refuses constant heads

- **What I did.** Probes `a14` `ok := true && f()`, `a15` `a[f()] = 5`, `a16` `a[f()] = "s"` (`decoder-constant-head-regression.txt`, `probe-shapes.tsv`): the classifier ADMITS each (design §1's letter: constants are operands; `&&` a guard; an element target a plan); the candidate frontend emits one `unseq` node (0 probes; `fe_rc=0`); the candidate `golean` REFUSES the wire: `unseq: head 'bool' … is outside the Stage C fragment (admitted heads: ident, index-get, slice, builtin-len, builtin-cap, binary, unary, type-assert); refused by name` (likewise `'int'`, `'string'`). Main's frontend + binary RUN all three (`main_default==cand_default = False` only on these three of 47 probes).
- **Why it matters.** Legal Go inside the pilot grammar that lowered and ran on main now returns `unsupported` — a coverage regression on the trusted surface, named at the point of failure (fail-closed, not a wrong answer). The design's §6 says the store value «must be a CELL: a constant or atom value is copied into one»; its §5 D8 lists no constant head. No corpus row has the shape (gate #2: NO PASS→non-PASS), which is why the gates did not see it.
- **Where.** `tools/nativefrontend/unseq_lower.go` `ensureCell` (the `copy` eval whose head is the constant wire; also `guard`'s `ensureCell(left, boolTy)` and `emitUnseqSweep`'s elem-assign `ensureCell(v, elemTy)`); `GoLean/NativeToIR.lean` `unseqCheckHead` (the `| other =>` arm).
- **Proposed disposition.** FIX-FIRST: admit `int` / `bool` / `string` constant heads in D8 (an `eval` of a constant is trivially in normal form — no read, no failure; D9 already checks the head type against the cell) with a positive wire test and a `mutants.tsv`/`check-wire-boundary` control; OR make the classifier decline a constant guard-left / constant store value to the legacy path (narrower coverage, no decoder change). Row the three programs either way.

### F3 — COHERENCE-GAP (decoder spec vs implementation; machine catches it dynamically) — D12's STATIC G does not confine a NESTED guard's completion binder to the OUTER region

- **What I did.** From the lowered graph of `c := (a && (b || f())) && g()` (`a18`, guards `guard1` ⊃ `guard3`), I made the completion `then` consume `$u3` — the INNER `||`'s completion binder, produced by `join5` (region `guard1`, not `guard1`'s completion) — instead of the outer `$u1` (`mutants.tsv`, `m02`/`m02b`). With `a = true` the wire DECODES and RUNS (exit 0, `f g` / 1); with `a = false` the decoder admits it and the machine refuses at run time: `unseq: the completion statement reads binder '$u3', which was not produced — its producer 'join5' was SKIPPED (confined to a disabled region) … malformed graph` (`unproducedConsumer?`).
- **Why it matters.** Design §5 D12: «a binder produced inside region G by an occurrence other than G's completion is consumed only by occurrences whose region chain contains G — never by a store, `then`, or an occurrence outside». `$u3` IS produced inside `guard1` by `join5` ≠ `guard1`'s completion; by the letter the wire is refused STATICALLY. `unseqConfinedTo?` (`GoLean/NativeToIR.lean`) exempts a binder whenever its producer is the completion of ITS OWN guard, ignoring that guard's enclosing region. Fail-closed (Stage B's F1 dynamic refusal holds), never emitted by the frontend (the emitter's outer join consumes the inner completion INSIDE the outer region), but the decoder-spec claim «STATIC G» is not met for nesting depth ≥ 2.
- **Proposed disposition.** Fix `unseqConfinedTo?` to confine a guard's completion binder to the REGION OF THAT GUARD (its `region`, if any) rather than to nothing; add `m02b` as a mutant (`invalid branch join`); one-line correction in design §5 D12 until then.

### F4 — RECORDS-CLAIM — «K=80» draws claimed for the lowered E13 rows; no `--slow` ran after the lowering

- **What I did.** `docs/2026-08-11_latitude-inventory.md` (E13 Stage C bullet): «The 24 E13 rows the pilot lowers keep gc's draw in their sets (K=32 and K=80)»; `docs/BUGS.md` BUG-112: «Both rows PASS with gc's draw inside the set on every K=32 draw (K=80 under `--slow`)». The evidence README's gate table has ONE `--slow` run — at C1 (`ccd3bdab` + C1 edits), BEFORE `unseq_lower.go` existed; C2 and C3 ran `ci --diff` (K=32) and the fast `ci`. `grep -n "K=80\|slow" c2-gate.txt c3-gate.txt` → nothing.
- **Disposition.** Reword both to K=32 (gate #2), or let the train's owed 5a `ci --slow` make the statement true and cite THAT run. (My own 20 draws per row — 5 × {GOMAXPROCS 1, 8} × {default, `-N -l`} — are in `gc-rows.tsv`; every draw is a member.)

### F5 — RECORDS-CLAIM (minor; part of F1) — the choice-trace analysis does not name what `r2b`'s difference from main IS

`choice-trace-c2.txt` / README §C3 classify `r2b` under «the 13 born rows» with an observation difference. For a STRICT singleton, a difference from main's default means main's legacy default is a NON-member — the F1 gap. Disposition: with F1.

### F6 — NIT — design §6 vs code: discard cells

Design §6: «a statement-position call with results gets DISCARD cells `$d<n>`»; `unseq_lower.go` `call()` mints `$u<n>` for every result (probe `a37`: `['$u3', '$u4'] := fv:two($u2)`, `lowered-graphs.txt`). Fix the sentence.

### F7 — NIT — BUGS.md ordering

`## BUG-112` is inserted ABOVE `## BUG-111` (`git diff … docs/BUGS.md`, hunk @@ -7002). `check-bugs.sh` passes (112 entries). Move it below BUG-111 at the fix round.

### F8 — NIT — decoder limitations the spec should state, not imply

(i) D8's «no hidden read» for `ident` heads and `ident` callees is RELATIVE to the frontend's privacy analysis: the decoder cannot tell a package-level variable from a private local by name (a hand-built `eval $u ident g` with `g` global decodes). (ii) D14 restricts `then` only by exclusion (no `unseq`, no `unseq-probe`, no `recover`); v2.1 §3.1's completion contract («stores and control transfer over results; no rerun of any source expression») is not checked — a hand-built `then` may hold arbitrary statements. Both hand-built-only; the trust for them lies in `unseqClassify`/`emitUnseqSweep`. Disposition: one sentence each in design §5.

### F9 — NOTE for (c) — the canonical slot is NOT gc's realization for TYPE ASSERTIONS to non-direct-interface types

gc's `order.go` copies `x.(T)` to a temp AT ITS LEXICAL POSITION (`ODOTTYPE` → `copyExprClear` when the result type is not pointer-shaped), so gc realizes the assertion EARLY — before any later hoisted call — while the canonical slot (calls first, reads late) realizes it LATE. Measured (`gc-rows.tsv`, `probe-shapes.tsv`): `assert-left-call` gc `` · conversion vs default `wit 5` · conversion; `assert-middle` gc `wit 1` vs default `wit 1 | wit 2`; `index-assert-left-call`; BUG-101's two rows; probe `a34` (`iv.(string) + f()`: gc `s!`, default the conversion panic). Every one is a MEMBER and every such row is a membership row; a STRICT row of this shape cannot pass silently (its default ≠ gc → red at `differential`). The design's «gc's realization where gc is call-first» is accurate; suggest naming this exception in §6 so a future strict row is not mistaken for a machine bug.

## 2. What was checked, with results

### (a) The decision procedure — shape probes (`probe-shapes.tsv`; 40 + 7 programs; each: census decision, wire, all-tape set, default tape, main-tip default, 20 gc draws)

| probe | shape | decision (calls/nonEvents) | §1 letter | set / gc |
|---|---|---|---|---|
| a01 | captured func-local callee `x := a + f()`, `a` captured by `f` | ADMIT 1/1 | ✓ | {11, 12}; gc 12 ∈; default = gc |
| a02 | shadowing `x := x + f()` (inner block) | ADMIT 1/1 | ✓ | {11, 12}; gc ∈; default = gc |
| a03 | address-taken parameter (`p := &x`, `*p = 5` in `f`) | ADMIT 1/1 | ✓ | {11, 15}; gc ∈ |
| a04 | nested composite literal with a call `[]int{f()}[0] + a` | LEGACY «composite literal» | ✓ | singleton; = main |
| a05 | pointer-receiver method call | LEGACY (named type / selector) | ✓ | singleton |
| a06 | call in index position `a[f()] + g()` | ADMIT 2/2 | ✓ | 2 members; E1 f→g; gc ∈ |
| a07 | map compound target with a call in the key | LEGACY «map» | ✓ | singleton |
| a08 / a09 | `defer h(f(), a)` / `go h(f(), a, done)` | LEGACY (statement form) | ✓ | singleton |
| a10 | `return f() + a[0], g() + a[1]` | ADMIT 2/4 | ✓ | 4 members; gc ∈ |
| a11 / a12 | select case expression / if-init | LEGACY (sub-accumulator) | ✓ | singleton |
| a13 | MIXTURE: admitted head + map operand `a + f() + m[1]` | LEGACY whole sweep, 0 `unseq`, 0 probe | ✓ never half-lowered | singleton |
| a14 / a15 / a16 | `true && f()` / `a[f()] = 5` / `a[f()] = "s"` | ADMIT, lowered, **decoder REFUSES** | letter ✓, **F2** | main ran |
| a17 | private compound fold: `x += f()`, `f` calls `g` which writes `x` | ADMIT (x address-taken → READ occurrence, not folded) | ✓ | {11, 110}; gc 110 ∈ |
| a18 | nested `(a && (b \|\| f())) && g()`, privates | ADMIT 2/3 | ✓ | singleton (all forced); = gc |
| a19 | nested calls `f(g(), a, h())`, `a` captured | ADMIT 3/1 | ✓ | {6, 15, 105}; gc 105 ∈ |
| a20 | `a[f()] = g()`, `f` REBINDS `a` (frozen header) | ADMIT 2/2 | ✓ | 2 members, both arrays' stores; gc ∈ |
| a21 | `x /= f()`, private | ADMIT 1/1 (the `/` may fail) | ✓ (all edges forced) | singleton |
| a22 | Go 1.22 loop variable captured, `a[i] + f()` | ADMIT 1/2 | ✓ | 2 members; gc ∈ |
| a23 | named result captured by `defer`: `r = a + f()` | ADMIT 1/1 | ✓ | 2 members; gc ∈ |
| a24 | `&x` taken, no capture; `f` writes `*p` | ADMIT 1/1 (x READ occurrence) | ✓ | {11, 19}; gc ∈ |
| a25 | slice parameter, callee mutates the element | ADMIT 1/1 | ✓ | {6, 105}; gc ∈ |
| a26 | func local reassigned by a sibling call `f() + g()` | ADMIT 2/1 | ✓ | singleton (forced) |
| a27 | guard inside args `f(a && g(), h())`, `h` sets `a` | ADMIT 3/2 | ✓ | singleton (E1 at completion) = gc |
| a28 | `println(a, f())` | ADMIT 1/1 | ✓ | {`1 10`, `2 10`}; gc `2 10` ∈ |
| a29 | `a[i] += f()`, `i` captured (BUG-104 class) | ADMIT 1/2 | ✓ | {823, 130}; gc ∈; `f` once |
| a30 | `len(a) + cap(a)*10 + f()*100`, `f` reslices `a` | ADMIT 3 events/1 call/2 | ✓ | singleton 142 = gc (len/cap E1-forced before f; gc agrees) |
| a31 | string indexing | LEGACY «index of a non-slice base» | ✓ | probe kept |
| a32 / a33 | `^a`, `!b` / `a<<n` non-constant count | ADMIT | ✓ | 2 members each; gc ∈ |
| a34 | `iv.(string) + f()`, `iv` captured, `f` sets `iv = 3` | ADMIT 1/2 | ✓ | {`s!`, conversion panic}; gc `s!` ∈; default ≠ gc (F9) |
| a35 | 3-index slice `a[0:hi:8]` in `len` | ADMIT 2/1/2 | ✓ | singleton |
| a36 | 9 checked reads + 1 call (ready set 10) | ADMIT 1/18 | ✓ | width 8: REFUSED BY NAME («site bound 10 exceeds the case's width 8»); width 16: «work cap exceeded» — never truncated (`n3-refusals.txt`) |
| a37 | call statement discarding 2 results | ADMIT 2/1 | ✓ | 2 members; gc ∈ |
| a38 | `a[f()]++` | ADMIT 1/2 | ✓ | singleton |
| a39 | `return two(a[0] + f())` (2-result forwarding) | ADMIT 2/2 | ✓ | 2 members; gc ∈ |
| a40 | interface parameter boxing `take(a, f())` | ADMIT 2/1 | ✓ | singleton (arg read forced before call… `a` private) |
| b01 / b02 / b03 | generic / variadic / imported-package callee | LEGACY «generic function callee» / «variadic callee» / «callee expression outside the pilot grammar» | ✓ | — |
| b04 | package-level variable operand `g + f()` | LEGACY «package-level variable» | ✓ | — |
| b05 | closure capturing `a` defined AFTER the sweep | ADMIT (conservative whole-body address-taken) | ✓ | — |
| b06 | tuple forwarding `add(two())` in the sweep | LEGACY whole (1 probe) | ✓ | — |
| c03 | define target captured by a LATER closure | ADMIT | ✓ | {12, 13}; gc 13 ∈ |

Every admitted sweep is inside §3.1's contract; every declined sweep names its construct; no coverage note beyond F2's three shapes. The mixture guard is never reached (the classifier declines the whole sweep first); the emitter's `value`/`call`/`readWrite` switches end in `unsup(...)`, never a fallthrough; `emitFuncLit` resets and restores `probeSuppress`/`hoisted`/`unseqBody` for a lifted body (`emit.go` ~7979–8016), so an immediately-invoked literal's body keeps its own legacy probes.

### (b) The lowering's edges (`lowered-graphs.txt`)

| check | graph | result |
|---|---|---|
| E1 through nested calls | a19 `f(g(), a, h())`: `call0 g`; `call2 h after=[call0]`; `read1 a`; `call3 f after=[call2]` args `($u0, $u1, $u2)` | ✓ g→h→f; the read unordered vs g, h |
| E1 into/out of a guard region | a27: `read0 a; guard1 test=$u0; call2 g region=guard1; join3 region=guard1; call4 h after=[join3]; call5 f after=[call4]` | ✓ anchored at the COMPLETION for the later `h`; entry has no earlier event to follow |
| nested `\|\|` inside `&&` | a18: `guard3.region=guard1`, `call4 f.region=guard3`, `join5.region=guard3`, `join6.region=guard1`, `guard7 after=[join6]`, `call8 g.region=guard7` | ✓ region chains; f → join5 → join6 → guard7 → g |
| N1 SPLIT / frozen header, bound once | a20 `a[f()] = g()`: `read0 $u2 := a` (one header read); `target2 $t4 :=T &$u2[$u3]`; `stores [($t4, $u5)]` | ✓ header producer separate from the plan; one slot; plan shared by the store |
| private-local compound fold | a17: `x` written by a sibling closure → `x` is address-taken → `read` occurrence, NOT folded; a21 private `x /= f()` folded | ✓ the fold applies only when no closure/`&`/method receiver reaches the local |
| target plan shared by load and store; index evaluated once | a29 `a[i] += f()`: `call3 f; read0 $u1 := i; target1 $t2 :=T &a[$u1]; load2 $u3 := load $t2; op4; stores [($t2,$u5)]`; BUG-104 rows: `f` printed once in every member | ✓ |
| canonical order = per-frame events then residual | every dump: event blocks first (each with its operand subtree), residual after; a06 `call1 f, call3 g, read0 a, access2, op4` | ✓ (D7 accepted every emitted graph) |

### (c) Canonical order vs gc

On every pre-existing row of the pilot's 25 packages the candidate's default tape equals main's (359 rows compared, `default-tape-comparison.txt`: 356 identical, 3 differ = `compound-call-target-vs-call`, `compound-call-target-vs-len` — the two designed fixes — and the born `r2b`, F1); main's strict rows PASS the differential, so every pre-existing strict row's default IS gc's. On the 29 rows I re-ran against gc (`gc-rows.tsv`) and the 47 probes, the default tape ≠ gc only on MEMBERSHIP rows of two classes: gc's EARLY type-assertion copy (F9: `assert-left-call`, `assert-middle`, `index-assert-left-call`, `a34`) and BUG-101's early read of a captured local (`assert-ok-early-len-hoist`, `slice-value-early-len-hoist`) — each gc draw a member. `len`/`cap` as E1 events matched gc where a later call reslices the operand (a30: 142 both). gc's `safeExpr` re-read (R4 `a[0] += mut()` rebinding `a`): gc draws `old 10 20 / a 101 200` = the header-read-AFTER member ∈ set. Methods and multi-target (L-016) are outside the grammar (legacy, unchanged).

### (d) Static vs dynamic refusals (`mutants.tsv`; 18 tracked mutants reproduced by `check-unseq-wire`, 18 of mine)

| edit | decoder (static) | machine (dynamic) | classification |
|---|---|---|---|
| duplicate binder across regions (m01) | `duplicate result` | (wellFormed? at ENTER — same check) | defence in depth |
| skipped-branch value through a join that is itself skipped — NESTED completion consumed by `then` (m02/m02b) | **ADMITTED** | RUNS when the outer region activates; `unproducedConsumer?` refusal when it skips | **F3** — decoder spec not met |
| target plan base = `ref a` (m03b) | D13 `non-atom base or index` | F2 `unseqUnfrozenPlan?` (shadowed) | defence in depth |
| `after` forward reference through a region (m04); guard after itself (m12); load ranked before its target (m11) | D7 `not a linear extension` | case (iii) «no ready occurrence» (shadowed) | defence in depth |
| binder without `$` (m05) | D2 `not a reserved $ slot name` | wellFormed? | same check |
| guard tests a TARGET binder (m06); target binder as a value (m13) | D6 `sort mismatch` | wellFormed? | same check |
| two results → one binder (m07); empty graph (m08); region names a non-guard (m16); completion produced outside its region (m10) | by name | wellFormed? / D3 | same check |
| `then` uses a region-confined non-completion binder (m09) | D12 `invalid branch join` | `unproducedConsumer?` (shadowed) | defence in depth |
| `to-interface` of a non-atom argument (m14) | D8 `hidden read in an argument` | — | static only |
| CONSTANT head (m15 = the frontend's own `copy` shape) | D8 `head 'int' … outside the Stage C fragment` | would run | **F2** — over-refusal of an emitted shape |
| control (a18 unchanged, m17) | decodes | runs `f g` / 1 | ✓ |

No decoder-admitted graph the machine refuses at run time was found other than F3's; no machine-admitted graph the decoder refuses other than F2's constant heads.

### (e) The set claims (`gc-rows.tsv`; 29 rows × 20 gc draws; the 53 checks via `check-unseq-wire`, `gates.txt`)

`scripts/check-unseq-wire` in this worktree: 51 fixtures byte-identical to `build.py`, «every reference set exact over the wire», 18 mutants refused by name in-process and through the CLI (72 ok lines; EXIT=0); the harness's expected members equal `outcomes.txt` line for line (W1–W6, R1 ± reduction, R2a–c ± entry anchoring, R4, R6 ± fused). My own enumeration of the 13 pilot rows reproduces every set with gc inside (`w1` {1,2} gc 2; `w2` {10,30,40} gc 40; `w3` gc `w3 10 21`·1021; `w5` gc the immediate panic; `w6` {0,1,2} gc 2; `r1` {0,1,2,3} gc 3; `r2a-*`/`r2b` singletons = gc; `r2c-true` gc `g k sink 1 true 7`; `r2c-false` gc `g k sink 1 true 7`; `r4` gc `old 10 20 / a 101 200`; `r6` {10,20} gc 20).

| moved / widened row | set (candidate, re-enumerated) | spec permission of each member | gc (20 draws) |
|---|---|---|---|
| `assert-right-call` `wit(5) + iv.(int)` | {``·conv, `wit 5`·conv} | the assertion is not a call: unordered vs `wit` (omission) | `wit 5`·conv ∈ |
| `multi-assign/index-target-rhs-call-order` `xs[i] = bump()`, `i` captured | {932, 1209} | spec#Assignment_statements phase 1 «usual order»: the index operand read vs the call unordered | 1209 ∈ |
| `noodler/latitude/args-index-vs-call` `g(a[0], f())` | {15, 1005} | «the order of those events compared to the evaluation and indexing of x … is not specified» | 1005 ∈ |
| `noodler/latitude/concat-var-vs-call` `s + f()` | {`ab`, `zb`} | read of a captured local vs call unordered | `zb` ∈ |
| `noodler/latitude/index-call-index` `a[0] + f() + a[2]` | {4, 103, 301, 400} | two reads vs one call, all unordered (read-vs-read by omission; R1) | 400 ∈ |
| `noodler/latitude/return-operands` `return v, f()` | {(1,5), (100,5)} | spec#Return_statements: operands «in the usual order» | (100,5) ∈ |
| `noodler/maps/slice-compound-call-mutates` `a[0] += f()` | {15, 105} | `x op= y` evaluates `x` once; its read vs `f` unordered | 105 ∈ |
| `assert-middle` (2→3) `wit(1) + iv.(int) + wit(2)` | {``, `wit 1`, `wit 1 wit 2`}·conv | only the two calls are ordered; the assertion may fall before, between, after | `wit 1`·conv ∈ (F9) |
| `index-middle` (2→3) | {``, `wit 1`, `wit 1 wit 2`}·[9] | as above for a checked read | `wit 1 wit 2`·[9] ∈ |
| `index-assert-left-call` (3→4) `s[i] + iv.(int) + wit(5)` | {``·conv, `wit 5`·conv, ``·[9], `wit 5`·[9]} | three mutually unordered occurrences; either failing operand may win | ``·conv ∈ (F9) |
| `two-index-left-call` (3→4) `s[i] + t[k] + wit(5)` | {``·[5], `wit 5`·[5], ``·[9], `wit 5`·[9]} | as above | `wit 5`·[9] ∈ |
| flips: `assert-ok-early-len-hoist`, `slice-value-early-len-hoist`, `compound-call-target-vs-call`, `compound-call-target-vs-len` | {`mut`·6, `mut`·conv}, {`mut`·12, `mut`·22}, {`f wit 5`·[9], `f`·[9]}, {``·[5], `f`·[5], `f`·[9]} | E1 `fnine → len → wit` keeps `wit` out of the third set (its operand `b[j]` panics first) | `mut`·6, `mut`·12, `f wit 5`·[9], `f`·[5] ∈ |

No member is forbidden by spec#Order_of_evaluation; every gc draw (plain and `-N -l`, GOMAXPROCS 1 and 8) is a member.

### (f) N3 refusal and the `depth=128` row

`a36` (ready set 10): at the corpus default width 8 → `site bound 10 exceeds the case's width 8 — the width assertion is REFUTED (mechanically, at pick position 0)`, EXIT=1; at width 16 / work cap 5M → `work cap exceeded after 4801014 step(s) … with subtrees still unexplored`, EXIT=1 — refusals BY NAME, never a silent sequentialisation or truncation (`n3-refusals.txt`). `continue-label`: w = 18 → 4·18 = 72 → 128 is the convention's value (design §3 predicted ≈11/64; §10 records the measurement). Exhaustive enumeration over ALL tapes closed at work cap 200M: **observations=1**, 32 805 leaves, 39.6M steps, maxdepth 18 (`continue-label.txt`); 20 random tapes at depth 128 and 20 at depth 512 give the same single observation `3140111 6011010 8193041` = gc. The declaration hides no variance; at work cap 20M the same enumeration refused by name.

### (g) Trust boundary

Decoder arm: every field read is `StrictJson.field` (required) or an explicit `o.get?` for the two optional keys `after`/`region`; `head.type` absent → refusal; no `getD`, no default that reconstructs metadata; exact keys per kind; `wellFormed?` runs at the boundary; D7/D12 as read. `check-wire-boundary`'s +7 controls reproduce through the real CLI inside `check-unseq-wire`. Frontend: `emitUnseqSweep` is reached only for an admitted sweep; every unmatched shape ends in `unsup(...)`; the mixture guard is double-checked (in the sweep and in the hook). Gaps: F2 (an emitted shape the decoder refuses), F3, F8.

### (h) Records

- Census recomputed with the candidate frontend over all 1354 `cases.tsv` packages (`census-recompute.txt`): 107 896 sweeps, **133 admitted / 29 packages / 0 in imported units**; forms 52 compound / 32 return / 26 assign / 12 define / 5 elem-assign / 5 call-stmt / 1 print-stmt = the design's 120 (50/32/26/7/5) + the 13 pilot sweeps; the 29 packages = the tracked 28 + `evalorder/unseq-pilot`.
- Whole-corpus dual emission (`dual-frontend-emission.txt`): 1354 packages; **25 wires DIFFER** (= exactly the 25 packages carrying `unseq` nodes), 1304 byte-identical, 25 both-refused with IDENTICAL refusal text; **117 `unseq` nodes**; legacy probes 123 → 91. Since `GoLean/GoCore/` is untouched (diff stat) and the `NativeToIR.lean` diff is additive (one `stmtAllowedKeys` row + the arm), a byte-identical `unseq`-free wire decodes and runs identically — the «0 rows differ outside the pilot» claim follows; the default-tape comparison above is the direct check on the 25 (+1 control) packages.
- Baseline (`git show 6a7beb3d:baselines/native-full.tsv` vs the candidate's, keyed on id): 13 added (the pilot rows), 0 removed, 11 changed = 4 FAIL→PASS/membership + 7 PASS/-→PASS/membership, exactly the listed rows; 3455 PASS / 244 FAIL; the header explains the run's 3454/245 (`google-search` red for the 5a-class STALE certificate only). The re-pin also sorted the data rows (main's file was not sorted).
- `check-bugs.sh` EXIT=0 (112 entries); BUG-101 fixed, BUG-102/104 Cases moves, BUG-112 Cases as claimed. Ledger §8 arithmetic: 3686+13 = 3699; 3438+13+4 = 3455; 248−4 = 244; reds 133+9+25+7+70 = 244 ✓. Inventory: E2/E12 «ENVELOPED on exactly these rows» — the wording is bounded to the named rows; E2 leaving §10 is justified (BUG-101 fixed, the value axis enveloped on its rows). Twin: `check-frontend-pins` ok — `e1a877251021…` byte-identical; stdlib pin 61 files ok.
- Gates reproduced here (`gates.txt`): `lake build` 96 jobs EXIT=0; `go test ./tools/nativefrontend` ok; `check-unseq-wire` PASS; `check-unseq-scheduler` PASS (24 required theorems, classical trio only); `check-frontend-pins` ok; `check-bugs` ok; `check-evidence-size` PASS.

### (i) Scope

No `GoLean/GoCore/` file changed; no Stage D economics, no Stage E family, no C3/C4/P, no NaN lane; the `lowerdiag` `causes.tsv` row is a vocabulary classification. The legacy path is byte-identical outside the pilot (above). The one scope item is F1's disposition (a Stage E fix, rowed now).

## 3. What I did NOT check

- A full `scripts/ci` / `ci --diff` / `ci --slow` (box-wide lock; not required by a finding — every focused gate reproduced green; F4 is about the CLAIM, not a suspected failure).
- The per-stream consumption dumps of `scripts/choice-trace-corpus` (the S3 method) on both sides; I reproduced the wire byte-identity and the default-tape observations instead (§2.h).
- K=80 gc draws; mine are 20 per row.
- Any Lean proof beyond the unchanged `GoLean/GoCore/` (diff stat) and the Stage B scheduler gate; the 5a certification step (owed to the train).
- gc's behaviour on shapes outside the pilot other than F1's (`||`/`&&` beside a later call).
- Stage D economics (cell allocation per iteration in the fmt shim loops) beyond the `continue-label` enumeration cost above.

## 4. Provenance

Every decision here is [AGENT]. The two ratification items — the E2/E12 value-axis envelope on the nine rows and the retirement of E13's residuals (1)/(9) on the pilot's rows — are the [USER]'s (PENDING [USER], handoff §6); the audit found every member of those sets spec-permitted and gc's draw inside each. No edit to the candidate or to `main`; no push.

## Re-verification (fix round `6886fe00`, 2026-09-20) — [AGENT] auditor

**REVISED VERDICT: MERGE-CLEAN.** The fix round (runtime `e73c706f`: `GoLean/NativeToIR.lean` D8 admits a bare constant head, D12 confines a nested guard's completion to its guard's region; records `6886fe00`) closes F1–F9 as dispositioned. Every re-run item below reproduced the worker's claim on my own probes and binaries; nothing new was found. The two ratification items stay PENDING [USER] (the E2/E12 value-axis envelope on the nine rows; the E13 narrowings (1)/(9) retired on the pilot's rows); the 5a certification stays owed to the train (the `--slow` run's `certificate provenance` red is exactly that item).

Bootstrap: `git checkout --detach 6886fe00` in this worktree; `.lake` refreshed by a plain copy from the candidate worktree at identical source; `scripts/capped lake build` → `Build completed successfully (96 jobs)`, EXIT=0 (`.tmp/warm2.log`); the fixed `golean` sha256 `90024323dbe00082…` = the sha the tracked `--slow` tail records; `tools/nativefrontend` is unchanged in the fix round and the rebuilt frontend binary is byte-identical to the candidate's (`cmp` clean) — so every wire below is the candidate's wire, only the decoder moved. Evidence: `docs/evidence/2026-09-20_unseq-stage-c-audit/reverify-*` (6 files, 28 KiB; `check-evidence-size` PASS on both trees).

| item | what I ran | observed |
|---|---|---|
| F2 — a14/a15/a16 on the fixed binary | `native-json-run` on the frontend's wires; `coverage-observations` over all tapes; main's frontend + main's binary beside | `x := true && f()` → 2; `a[f()] = 5` → `f`·59; `a[f()] = "s"` → `f`·"xs" — byte-identical to main's observations, each an all-tape singleton (`reverify-f2-probes.txt`) |
| F2 — the three corpus rows | `scripts/capped scripts/diff-one` on the six new rows | `evalorder/unseq-const-cell/{const-guard-left,elem-assign-const-int,elem-assign-const-string}` PASS strict (the tracked `--slow` tail: `wide=0/3/2 exhausted=none depth=fixed`) |
| F2 — D9 still refuses a mistyped constant | crafted: `cguard`'s constant copy with an `int` head into the bool cell; a `bool` head annotated `int`; a constant head with no `type`; a constant head missing `value` | `head type … int … disagrees with cell '$u0' declared … bool; refused by name` (both); `the eval head … carries no type … refused by name`; `missing field 'value'` — all EXIT=1 (`reverify-f3-d9-d12-probes.tsv`) |
| F3 — m02/m02b on the a18 graph | the unchanged mutant files through the fixed CLI | BOTH now refuse at DECODE: `invalid branch join … the completion statement uses '$u3', confined to the region of 'guard1'; refused by name` (EXIT=1); the m17 control still runs (`f g`·1, EXIT=0) |
| F3 — the 19th mutant | `mut-nested-completion-join.json` for `r2cTrue` and `r2cFalse` | both refuse statically: `'call9' uses '$u4', confined to the region of 'guard2'` |
| F3 — no over-refusal | crafted a LEGITIMATE cross-region join: the inner `\|\|`'s completion consumed by an extra op INSIDE the outer `&&`'s region (not the outer join); the R2a wire (a top-level completion consumed by the invoke); a 3-deep Go program `(a && (b \|\| (c && f()))) && (g() \|\| h())` through the emitter | all decode and run: the crafted join `f g`·1 (= the unmutated graph), R2a `guard k / guard result true 7`, the 3-deep program admitted (3 calls / 6 non-events, 13 region-tagged occurrences), all-tape singleton `f g`·1 = gc `f g 1` (`reverify-three-deep-guards.txt`); an inner completion consumed by a TOP-LEVEL occurrence is refused (`'top' uses '$u3', confined to the region of 'guard1'`) |
| F3 — the dynamic refusal still present | `scripts/check-unseq-scheduler` (Stage B tests unchanged) | PASS — 24 required theorems, classical trio only; `GoLean/GoCore/` untouched in the fix round (diff stat) |
| the 18 + 1 mutants, r2a/r2c wires | `scripts/check-unseq-wire` (captured) | PASS, **80 ok lines, 19 mutants** refused through the CLI, 51 + 6 fixtures byte-identical to `build.py`, every reference set exact incl. `CGUARD`/`CELEM`/`CSTR` hand-built and native ([2]; `f`·59; `f`·1 — the witness programs return these); EXIT=0 |
| `check-wire-boundary` | captured | PASS — `11 byte-level controls + 9 unseq-node controls`, incl. the constant-head positive (`cguard` answers 2) and `unseq-nested-completion`; 20 ok lines; EXIT=0 |
| F1 / BUG-113 | `diff-one` on `evalorder/legacy-logical-vs-call/*`; `scripts/check-bugs.sh`; the entry read | `or-vs-call`, `and-vs-call` FAIL/differential (Lean `logical true 0`, Go `logical false 0`); `call-first-control` PASS; `check-bugs: ok (113 bug(s))`, EXIT=0 — the `wrong-answer 0/0` backlog line counts UNTRIAGED ids only (BUG-113's rows sit on its Cases line); the entry: Status open, Pinned-by differential, WHERE names main = candidate and the `r2b` difference, FIX PLAN names Stage E (with the interim legacy anchoring) |
| F5 | handoff §4/§10, README §C3 | the born `r2b`'s difference from main is named as main's spec-forbidden legacy default (handoff l.162/272, README l.136) |
| baseline delta over `2dac6a75` | order-insensitive compare keyed on id | **exactly six added** (`unseq-const-cell/*` 3 PASS/-, `legacy-logical-vs-call/{or,and}-vs-call` FAIL/differential, `call-first-control` PASS/-), 0 removed, 0 changed; header `# cases: 3705 (3459 PASS / 246 FAIL)` with the fix-round reason |
| F4 — the `--slow` claim | the tracked tail `fixround-gate-tail.txt` | `GATE END … EXIT=1 WALL=954s`, `membership_draws 80`, run 3705 = 3458/247 = the pin with `imported-goose/channel/google-search` red for the STALE certificate (`NativeToIR.lean`), DRIFT = that one line, `certificate provenance` FAIL = the 5a item, every other step ok; BUG-112's two rows `draws=80 (K=80; …)` with gc's one member every draw — the K=80 statements in the inventory (l.1679–1681) and BUG-112 (l.7174–7176) now cite THIS run; F4 is true |
| default tapes, the 25 pilot packages | my `.tmp/deftape` driver, fixed binary vs main's frontend + binary | 359 rows: 356 identical, 3 differ = `compound-call-target-vs-call`, `compound-call-target-vs-len`, `r2b` — unchanged from the audited tip (`reverify-default-tape-comparison-fixround.txt`) |
| trace subset outside the pilot | 55 non-pilot packages / 123 rows / 4 streams (default + three fixed `--choices` streams), main's frontend + binary vs the fixed tree | **492/492 (row, stream) observations byte-identical; 55/55 wires byte-identical** (`reverify-outside-pilot-subset.txt`) |
| F6–F9 records | greps | design §6 `$u<n>` (the `$d<n>` text corrected, l.213); BUG-110 < 111 < 112 < 113 in file order; design §5 states the two decoder limits (ident privacy is the frontend's; `then` restricted by exclusion — l.192–199); gc's EARLY type-assertion copy recorded in design §6 (l.242) and the inventory E13/E2 (l.825–826) |
| anything new | D8's new arm admits only `int`/`bool`/`string` tags, no operands, typed by D9; the `| other =>` arm still refuses everything else | no new admission beyond the constant; no over-refusal found (above) |

Not re-run: a full `scripts/ci`/`ci --slow` (the tracked tail was read, its `golean` sha matches my build); `go test ./tools/nativefrontend` (the frontend is byte-identical to the audited candidate's, on which it passed); the choice-trace dump method itself (replaced by the 4-stream observation comparison above).
