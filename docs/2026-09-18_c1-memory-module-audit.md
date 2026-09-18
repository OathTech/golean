# Adversarial audit — C1 memory module + access trace, S0–S2b (branch `core/c1-memory-module-0918`, parked at `a8ada3cc`)

**VERDICT: FIX-FIRST (records-class).** No WRONG-ANSWER, no FOOTPRINT-LIE, no UNSOUND-PROOF, no
gate WEAKENING, no FAIL-OPEN introduced by the branch. The five runtime commits are semantics-
preserving on every well-formed program this audit could construct (34 scratch subjects, all SAME
on main's and the candidate's binary and all matching `go run`); the labelled coherence, the
`HeapNormal` preservation family and the deleted D6 theorem say what the handoff says they say;
the gate lines, choice-trace byte-identity, trace-equality audit and benchmark targets reproduce.
What must be fixed before the branch is a mergeable unit is RECORDS: (F1) the D1–D7/D9/D10
«RULED [USER] by default acceptance» provenance has no [USER] text in the record it cites;
(F2) the detector-soundness gc-side failure is MISDIAGNOSED — it is a pre-existing bug in the
lane runner, not the sandbox, and the HOLE cell IS judgeable here; (F3) the memory module's
docstring claims a byte-identity «on every normal cell» that is false (Lean witness), a refusal-
class change not disclosed. Everything else is NIT or pre-existing.

Auditor: [AGENT] (Fable), worktree `.claude/worktrees/audit-c1-memory-module`, branch
`review/c1-memory-module-0918` at the candidate tip `a8ada3cc` (main `68b261e6`). Ordered by
[USER] Mike 2026-09-18, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «(1) Agree,
run the audit.» Nothing merged, pushed, or edited on the candidate or main. Every logged decision
below is [AGENT]; items that are the user's are marked PENDING [USER]. Evidence (small):
`docs/evidence/2026-09-18_c1-memory-module-audit/`.

Binaries: main `231df9a9…` (the primary's certified `.lake/build/bin/golean`, read-only copy);
candidate `e0d47b48…` (this worktree's build at `a8ada3cc` from a plain copy of the candidate
worktree's `.lake`; `scripts/capped lake build` EXIT=0, 96 jobs, 0 warnings); S2a `d4c0c14d…`
(`git archive 7f7c721c` built in `.tmp/s2a`, 39 modules recompiled, EXIT=0, 0 warnings).
Frontend: `tools/nativefrontend` at the tip (unchanged on the branch), `go1.26.5`.

## 0. Bootstrap and static checks (captured exits)

| check | command | result |
|---|---|---|
| deps | `scripts/setup-deps --from /home/dev/projects/golean` | EXIT=0 (go pinned `c19862e5f8`) |
| warm build | `scripts/capped lake build` | EXIT=0, 96 jobs, 0 warnings |
| core totality audit | `scripts/capped bash scripts/check-core-audit` | EXIT=0 — 45 modules (36 under GoCore), 51 required theorems, 15,553 declarations, **classical trio only**; 5 typed controls rejected as designed (`core-audit.log`) |
| escape hatches in the runtime diff | `git diff 68b261e6..a8ada3cc -- GoLean Tests \| grep '^+' \| grep -E 'sorry\|axiom\|native_decide\|partial\|admit\|unsafe\|implemented_by\|opaque\|maxHeartbeats\|decide'` | 0 hatches; 4 `decide`s, all on closed Bool facts (`Int.pow_pos (by decide)` ×2, a kind-pair `absurd … (by decide)`, and the pre-existing test `StateWf … illTyped := by decide`) |
| evidence size / alias | `scripts/check-evidence-size`; `scripts/check-agents-alias` | EXIT=0 / EXIT=0 (lane dir 264 KiB; 0 new offenders) |
| bug index | `bash scripts/check-bugs.sh` | EXIT=0 |
| untouched trust surface | `git diff --stat 68b261e6..a8ada3cc -- scripts tools Corpus baselines GoLean/NativeToIR.lean lakefile.toml lean-toolchain` | empty — the branch touches only `GoLean/GoCore/**`, `GoLean/CLI.lean`, `GoLean/ChoiceTrace.lean`, `Tests/**`, docs, evidence, `spikes/` |
| D8 marker | `git grep NPDRFReduction -- GoLean Tests` | the definition + docstring mentions only; 0 uses; build 0 warnings |
| D10 wording | `Store.lean:55` | «(allocation goes through `Store.alloc` only)» |
| `fun_cases` | `git diff … \| grep fun_cases` | 0 added/changed uses (13 pre-existing in the tree, untouched) — nothing to sample |

## 1. Findings, by severity

### F1 — RECORDS-CLAIM (provenance): «D1–D7, D9, D10 RULED [USER] by default acceptance» is not supported by the record it cites — PENDING [USER] ratification

- What I did: `grep -n -i 'default acceptance\|default-acceptance\|D1–D7\|raised no objection' docs/2026-08-31_qrow-rulings.md` → **0 hits**; the section «The on-deck decisions ruling record (2026-09-18)» (line 534 ff.) records exactly rulings (1) sequencing, (2) NaN, (3) 32-bit, (4) NPDRF/D8 — and nothing about D1–D7, D9, D10.
- Where the claim lives: charter `docs/2026-09-17_c1-memory-module-charter.md:173` («RULED [USER] 2026-09-18 (record: … «The on-deck decisions ruling record (2026-09-18)»): the coordinator's triage classed D1–D7, D9, D10 as … defaults and the [USER] raised no objection»), already on main at `68b261e6` ([AGENT] coordinator's commit); the handoff §0 and the slice log repeat it; the handoff §5 table then treats D1–D7 as the lane's brief.
- Why it matters: the global charter says failing to distinguish [AGENT] from [USER] decisions «is by definition a critical trust failure»; D1 (root cells), D2 (dense array), D3 (`HeapNormal` + `alloc` normalizes — a candidate BEHAVIOUR change), D5 (label on `Step`/`StepM`), D6 (theorem + audit), D7 (BUG-041 stays FAIL), D9 (S2c's shape) are [AGENT] recommendations that are recorded as [USER] rulings on the strength of silence. This is the pattern memory already flagged (2026-09-07 L3 audit: «user decisions never briefed as defaults»).
- Not the lane's edit (the header is the coordinator's, on main) — but the branch is not a mergeable unit until the rulings it implements are the user's.
- Proposed disposition: at the merge sign-off the [USER] ratifies D1–D7, D9, D10 explicitly (one line each or one line for all), the coordinator adds that verbatim to the qrow record, and the charter §7 header is re-tagged to cite it. Until then the header should read PENDING [USER] ratification. [AGENT]

### F2 — RECORDS-CLAIM (misdiagnosis) + PRE-EXISTING TOOLING BUG: the detector-soundness gc side did NOT die in TSan — the lane runner never creates the crash-hook files, so every `-race` harness exits 78 by design; the HOLE cell IS judgeable here

- Handoff §6 item 2 / evidence README «S2b — detector-soundness»: «the gc `-race` binaries the runner builds die at TSan's sync-allocator growth with EXIT 78 and no report (rlimits unlimited, overcommit 0 — the reservation is refused by the sandbox)»; slice log and §6c repeat «the gc side does not run here».
- What I did:
  1. `scripts/detector-soundness --select in-scope --jobs 6 --out artifacts/detector-soundness-audit` with the candidate binary → EXIT=2, 639 rows: `gc-no-verdict` 544 / `uncertified` 86 / `refused` 9 (`detector-soundness-unpatched-summary.txt`) — the lane's result reproduced.
  2. A row's `-race` harness run directly: `rows/atomics__counter__add/go/golean-race-bin` → **EXIT=78, empty stderr**. `go run -race` of my own program in the same sandbox → EXIT=1 with two `WARNING: DATA RACE` reports; `go build -race` + direct run → EXIT=66 with the report. So TSan runs here.
  3. `grep -n 'Exit(78' tools/coverageharness/crashhook.go` → lines 109–112: the generated `zz_golean_crash.go` opens `oracle.crash` with `O_WRONLY|O_TRUNC` (no `O_CREATE`) and `os.Exit(78)`s on failure — «Exit 78 is a setup failure, never an observation of subject behavior» (crashhook.go:99). `scripts/diff-coverage:1305` pre-creates both files before every run; **`scripts/detector-soundness` never does** (`grep oracle.crash scripts/detector-soundness` → nothing). The row dir indeed has no `oracle.crash`.
  4. `: > oracle.crash; : > oracle.registered` in that row dir, same env as the runner (`GOMAXPROCS=8 GODEBUG=panicnil=0 GORACE=exitcode=66`) → **EXIT=0** with the observation `{"schema":"golean-observation-v1","status":"ok","values":[…5]}`.
  5. A patched COPY of the runner (`.tmp/detector-soundness-fixed`: two `: >` lines before each `-race` run; ROOT pinned to this worktree; the tracked script untouched) run against the candidate binary: see §1a below.
- Why it matters: the handoff's PENDING [USER] item 2 asks the user to run the gc side elsewhere for a reason that is false; the «sandbox» story would have sent the check to another box and left a one-line runner bug in place. The runner is untrusted lane tooling (not a gate), so this is RECORDS + tooling, not trust-surface — but «HOLE = 0» is the S2b exit criterion the charter §6 names, and it was declared UNJUDGEABLE on a misdiagnosis.
- Proposed disposition: the lane fixes `scripts/detector-soundness` (mirror `diff-coverage:1305`), re-runs `--select in-scope` at the S2b-ii tip officially, reads HOLE/possible-HOLE off `summary.txt`, and corrects the handoff §6 item 2, §6c and the evidence README paragraph; the «TSan sync-allocator» sentence is withdrawn. [AGENT]

#### 1a. The patched-copy run (audit evidence, not the lane's record)

`bash .tmp/detector-soundness-fixed --select in-scope --jobs 6 --out artifacts/detector-soundness-audit-fixed`
(binary = this worktree's `.lake/build/bin/golean` at `a8ada3cc`, `e0d47b48…`; 19:00–19:24 UTC; the
tracked `scripts/detector-soundness` untouched): **EXIT=2 (INCOMPLETE — 9 `refused` rows, the
`params-omit-sites=` membership refusals the lane also had, plus 86 uncertified)**; 639 rows:
**agree-DRF 502 / agree-race 36 / over-refusal 6 / refused 9 / uncertified 86; HOLE rows: NONE;
possible-HOLE rows: NONE** (`detector-soundness-patched-summary.txt`). The 6 over-refusals are
`race/free/array-dyn-index-read-write` (BUG-041, the O1 residual — over-refusal 1 in the 2026-09-02
matrix, by design) and five `race/gomem-only/*` rows (the DESIGNED go_mem-RACY / TSan-GREEN
divergence, RULED [USER] 2026-09-02 option (A), BUG-084 `Cases:` line). So the charter §6 S2
exit check «HOLE = 0» HOLDS on the candidate binary — by this audit's patched-copy run, which the
lane should reproduce with the fixed tracked runner before recording it as the branch's own
evidence. The 86 uncertified rows are the machine side's ENUM-FAIL classes the lane already
recorded (deadlock members, frontend-quarantined subjects, a fuel truncation) — gc green or no
verdict there, none exit-bearing.

### F3 — COHERENCE-GAP (docstring false) / undisclosed refusal-class change: `storeLoc`'s claimed byte-identity «on every normal cell» is FALSE; the leaf-descent refusal is reachable under `HeapNormal`

- Claim: `GoLean/GoCore/Ops.lean:1386-1396` — «the result is byte-identical to the former «rewrite the root, normalize the whole root» on every normal cell … the one NEW refusal is the leaf-type descent's (`Ty.stepDown`), reachable only on a cell whose declared type has no component where its value has one — impossible under `HeapNormal`.»
- What I did: `.tmp/probe/IfaceCell.lean` (`scripts/capped lake env lean`, EXIT=0; evidence `probe-IfaceCell.lean`/`.log`): a store with ONE cell `.value (.interface ⟨"any"⟩) (.array #[int 0, int 1])`.
  - `#eval HeapNormal ctx0 ifaceStore` → **`true`** (`isNormalForTyTy (.interface _) _ = true`, Ops.lean:1305 — an interface-declared cell is normal with ANY value).
  - `#eval loadLoc … (.index (.base 0) 0)` → `ok (int 0)` (the read path unchanged).
  - `#eval storeLoc … (.index (.base 0) 0) (.int 5 .int)` → **`error (stuck "leaf descent: the declared type has no element type")`**. Main's leaf-first `storeLoc` (`68b261e6:Ops.lean:1374-1396`) on the same state: load base → `arraySet` → store root → `normalizeValueForTy (.interface _)` = identity → **`.ok`**.
  - The struct twin (`.interface` cell holding `.struct main.A`, path `.field … "f"`) → `HeapNormal` true; candidate `stuck "leaf descent: the declared type has no field f"`; main `.ok`.
- Reachability: I could not construct a Go program that path-writes INTO an interface-typed cell (interface contents are not addressable: `x.(T)[0] = v`, `s.i.(T).f = v` are compile errors; method calls copy or go through pointers). 13 leaf-write probes incl. nested array-in-struct-in-array, `.defined` chains, slice-header writes past `len` within `cap`, out-of-range paths, nil into interface/func/chan slots: all SAME on both binaries and equal to `go run` (`scratch-leaf-*`). So: unreachable from well-typed Go as far as this audit can tell; a refusal-CLASS change (ok → stuck) on a machine state the invariant admits.
- Why it matters: the S1 record discloses exactly one refusal-class change (unbound root under a path → `.internal`); this second one is undisclosed and the docstring asserts the opposite. The soundness argument for skipping the whole-root re-normalization is «`HeapNormal` ⇒ identical result»; it is true for every cell whose declared type HAS the component (the `Ty.stepDown` descent then mirrors `normalizeValueForTyAt`'s bound — I checked the `.array`/`.defined`-chain arithmetic by hand, Ops.lean:1432-1452 vs 1212-1224) and false for the catch-all types (`.interface`, and the `_, _ => true` arm: `.bool`/`.string`/`.pointer`/`.slice`/`.map`/`.chan`-holding-non-chan… — of which only `.interface` can plausibly hold an array/struct).
- Proposed disposition (records + one of two code shapes, [AGENT] recommends the first): (i) correct the docstring — «byte-identical on every normal cell whose declared type has the component; on an interface-declared (or catch-all-typed) root a path write now REFUSES by name where the former path succeeded — unreachable from Go, disclosed» — and add the class to the S1 disclosure list; or (ii) make `Ty.stepDown` return `(.interface id, b)` for an `.interface`-declared type on either step (the normalizer's own arm is the identity there), restoring the old behaviour. (ii) is a semantic edit that re-gates S1; (i) is records. Test to pin either: the `#eval` above as a `Tests/` pin.

### F4 — RECORDS/NIT (proof-argument gap, true by inspection): the deleted theorem's header infers «on a step that became panicking (both record nothing)», which its statement does not imply

- `6bb1930d:GoLean/GoCore/AccessTableEq.lean` header (lines 21–24) and handoff §5 «the fold's one corner»: the old fold recorded NOTHING on a step whose successor is panicking from a non-panicking pre-configuration; the new fold records the label; «by this theorem the two agree … on a step that became panicking (both record nothing)».
- The theorem (line 1229): `Step ctx c s c' s' tr → tr = tableTrace (stepAccesses ctx s c) ∨ (tr = [] ∧ c'.isPanicking = true)`. With `c'.isPanicking` the FIRST disjunct is still available, so the statement admits a non-empty label on a panicking successor — the sentence needs the extra fact «pre non-panicking ∧ post panicking ⇒ tr = []», which is nowhere stated.
- It IS true by inspection of the rules: every `Step` rule whose successor is `.panicking` from a non-panicking configuration carries `[]` — the `deliver`/`deliverS` panic branch (`StepFn.lean:64`, `Machine.lean` `deliver`), and the direct constructions in the `Step` block — `callValCalleeNil`, `callValArgsNil`, `frameDeferNilFall`, `frameDeferNilReturn` (nil-deref panics), `panicArgValue` (`panic(v)`), `panicResumeContinue` (`.next (.panicResumeK …)`) — all `… s []`; `stepFn`'s direct `.panicking` constructions all carry `[]` (`StepFn.lean:131, 265, 282, 286, 324, 612, 633, 660, 799`). The sync arm's `.wgAdd` negative-counter `.panicking` outcome is a sync-WORD write (label `[]`, S2c's account), not `.data`.
- Proposed disposition: records — say «by inspection of the rules (list)» rather than «by this theorem», or add the one-line lemma when S2c restates the label. No verdict moved (the corpus audit and the theorem both hold).

### F5 — RECORDS: cross-reference typo — evidence README line 201 says the alias finding is «filed as BUG-091»; the entry is BUG-111 (BUG-091 is an unrelated frontend-export bug)

- `grep -n BUG-091 docs/evidence/2026-09-18_c1-memory-module/README.md` → :201; `grep -n '^## BUG-091' docs/BUGS.md` → :5632 (goto quarantine text nondeterminism). Fix the number.

### F6 — NIT (records): handoff §1 table rows are out of chronological order (S0, S2b-ii, S2b-i, S2a, S1); the S2b-i «gated tree» identity is argued from a pre-chain snapshot + mtimes + binary hash (disclosed honestly in §2) — acceptable, but the next park should snapshot AFTER a full `git add`.

- Also stale: `GoLean/GoCore/MultiWfSound.lean:36` still says «so `MultiWf ctx m` is context-free» (B7's prose); C1 S1 made `MultiWf` read the context again for `HeapNormal` (`def MultiWf (m) := StateWf ctx m.shared ∧ …`, Multi.lean:2546; handoff §5 «`MultiWf`»). Refresh the docstring.

### F7 — COHERENCE-GAP (low) / proposal: after the table's deletion nothing MECHANICAL guards the emit/peek discipline

- The question (c): which side is trusted now — the TRACE, by construction. What checks it: `stepFn_sound`/`step_complete` (kernel-checked: the relation's label IS `stepFn`'s trace, same order, no `∃ tr`), `HeapNormal`/`StateWf` preservation, and the `Mem.*` wrappers' definitions. What does NOT exist any more: any check that every user-memory access goes through an emitting operation. A future `loadLoc ctx`/`storeLoc ctx` call added at a data site is a silent peek/raw write — exactly the class the table's «lockstep obligation» used to catch by disagreement. The handoff §5 («the emitting operations») says so itself: «the standing check … is the S2a audit while the table exists, review after».
- Census at the tip (raw `loadLoc ctx`/`storeLoc ctx` call lines): Machine 10/14 (main 18/29), StepFn 0/0 (1/1), Multi 2/4 (2/4), Ops 2/1 (4/0), Race 0/0 (2/0). The 14 raw `storeLoc` sites in Machine are the sync-word stores (:3653–3794, :3952), `storeMany` (:735, DEAD — no caller; `HeapNormal.of_storeMany` keeps it alive as a theorem subject) and the atomic RMW (:3982) — all outside the `.data` account by the docstring's own list. Consistent today.
- Proposed disposition: a cheap standing check — a pinned inventory of the raw call sites (file:function) diffed by `scripts/ci` (fail on a NEW raw site until it is classified in the module docstring), or a `Tests/` pin that greps the same. Not gate weakening; it replaces the retired instrument with something. [AGENT] proposal, not a blocker. Also: delete the dead `storeMany` + its lemma in S3 (owed cleanup).

### F8 — PERFORMANCE (disclosed by the lane, confirmed): `append_grow` successive ×2 ratios miss the ≤ 2.2 target; cost B (alloc_new, the (h) phase) unchanged

- See §4. The lane reported ×2.5–2.8 (MISSED, same mechanism as cost B); this audit measured ×1.6, ×3.5, ×2.1, ×2.8 under load, and 29.45 s → 0.31 s at n = 4,000 interleaved at load ≈ 1. Honest as recorded; S3's.

### F9 — (m) PRE-EXISTING, not C1's: a whole-struct copy through a struct-tag-compatible pointer alias refuses on BOTH binaries where Go accepts

- `scratch-retag-main.go`: `a := A{1}; p := (*B)(&a); q := *p` → both binaries `stuck "struct value type mismatch: expected main.B, got main.A"` in five shapes (copy, param, range element, `*new(B) = *p`); `go run` prints `1 1 1 8 3 5`. Field access through the alias (`p.f = 5; a.f`) works on both (5). Not in BUGS.md (`grep 'struct value type mismatch' docs/BUGS.md` → one unrelated mention). SAME on both, so not C1's drift — but it bounds BUG-111's proposed row (which uses field accesses, correctly) and is a fidelity gap for whoever owns L7. Proposed: a BUG entry + red-first row by a corpus lane.

### F10 — BUG-111 CONFIRMED end-to-end (the lane's entry is accurate; fix PENDING [USER])

- `scratch-bug111-main.go`: `go run -race` → EXIT=1/66, exactly 2 reports (`aliasRace`, `plainRace`); `aliasDisjointFields` clean (`scratch-bug111-go-race.txt`). The candidate AND main: `aliasRace` **status ok, value 1** (accepted — fail-open, pre-existing), `plainRace` **status race** (refused), `aliasDisjointFields` ok (3). The proposed red-first row and its must-stay-green guard are validated as shaped. Fix option (i)/(ii): PENDING [USER] (handoff §6 item 1), untouched here.

## 2. (a) `HeapNormal` and the in-place leaf write — scratch table

Invariant as STATED: `StateWf σ := Store.locSup σ ≤ σ.nextAddr ∧ HeapNormal ctx σ` (StateWf.lean:673-674); `HeapNormal s := Heap.normalB ctx.types s.heap = true`, `HeapCell.normal (.value ty v) = isNormalForTy types ty v` (Ops.lean:1523-1534). Note it is SELF-NORMALIZED-ness (normalize is the identity), not heap typing: the catch-all arms admit any value at `.bool`/`.string`/`.interface`/… (Tests/GoCoreContract.lean `address_bound_admits_ill_typed` pins this by `decide`). Preservation: `HeapNormal.of_alloc` (StateWf:2603), `.of_storeLoc` (:2924, via `writeAt_isNormal` :2866 — a path induction with `writeAt_isNormal_array/_struct`), `.of_storeMany` (:2946), `.of_storeMapPayload`/`.of_storeChanPayload` (:2611/:2622), `.of_allocCell` (:2588); folded into `step_preserves_wf` (:7937) over `MachineWf`. `isNormalForTy_sound` (:1607) gives `isNormal → normalize = ok v` (the direction the argument needs). There is NO theorem «new `storeLoc` = old `storeLoc` on `HeapNormal` states» — and F3 shows it is false as the docstring states it; the regression is the differential + choice trace, as the charter said.

| # | program (`docs/evidence/…/scratch-*.go`) | targets | main | cand | go | verdict |
|---|---|---|---|---|---|---|
| 1 | `narrowByte`: `b[2] = byte(300)` | width-narrowed leaf | 44 | 44 | 44 | SAME |
| 2 | `narrowInt8`: int8 overflow into `o.inners[1].arr[3]` | narrowing at depth 3 | −128 | −128 | −128 | SAME |
| 3 | `nestedLeaf`: `arr[1].inners[2].arr[0] = 9; .f = 2.5; arr[0].tag` | array-in-struct-in-array | 18 | 18 | 18 | SAME |
| 4 | `nilIface`: nil then `5` into an interface field | interface slot | 6 | 6 | 6 | SAME |
| 5 | `nilFuncChan`: nil func + nil chan fields, then a func | `.chan` nil canonical form | 7 | 7 | 7 | SAME |
| 6 | `pastLenWithinCap`: `s[:5][4] = 7` on `make([]int,2,5)` | header past len within cap | 9 | 9 | 9 | SAME |
| 7 | `outOfRange`: `a[3] = 1` recovered | out-of-range path | 42 | 42 | 42 | SAME |
| 8 | `sliceStructInnerArr`: `s[2].arr[1] = -5` | slice → struct → array | −2 | −2 | −2 | SAME |
| 9 | `definedChain`: `type T2 T1; T1 [3]int`; `x[1]`, `y[1][2]` | `.defined` hops in `Ty.stepDown` | 11 | 11 | 11 | SAME |
| 10 | `namedIface`: `var s Str` read-only then assigned | alloc at a named interface type | 4 | 4 | 4 | SAME |
| 11 | `lenCapPtrArr`: `len/cap` of nil and non-nil `*[N]int` | (d) tightening | 7755 | 7755 | 7755 | SAME |
| 12 | `wholeThenLeaf`: whole store, leaf write, whole read | root vs leaf | 3 | 3 | 3 | SAME |
| 13 | `ptrToLeaf`: `p := &o.inners[2].arr[3]; *p = 11; q.arr[3]++` | pointer to a deep leaf | 12 | 12 | 12 | SAME |
| 14–20 | `scratch-nilchan`: `&S{c: nil}`, `[2]chan int{nil,…}`, `takeChan(nil)`, `range []chan int{nil,nil}`, select on nil field, `&S{f: nil}`, captured nil chan | `alloc` normalizes (the `.chan` arm is the one REWRITING normalizer arm) | 7 6 1 3 9 6 1 | same | same | SAME |
| 21–26 | `scratch-retag`: `q := *p` through `(*B)(&a)` in 5 shapes + `p.f = 5; a.f` | `alloc` retag at `.allocNew`/`bindParams`/`bindIterVars` | stuck ×5, 5 | stuck ×5, 5 | 1 1 1 8 3 5 | SAME (pre-existing gap F9) |
| L1 | Lean: `.interface`-declared cell holding `.array`, path `.index 0` | F3 | old: ok (by definition) | **stuck (leaf descent)** | n/a | DIFF — unreachable from Go |
| L2 | Lean: `.interface`-declared cell holding `.struct`, path `.field` | F3 | old: ok | **stuck** | n/a | DIFF — unreachable from Go |

Does `alloc` normalizing move any observation? Not on any program here; the lane's S1 checkpoint gate (representation + `alloc` normalizes WITHOUT the conjunct) was already at zero drift. I could NOT construct a Go program that delivers a non-normal value to `Store.alloc` (every producing op normalizes at its own kind; nil literals arrive typed from the frontend; the tag-mismatch case is refused upstream, F9). «Zero drift is really zero» is therefore: zero on the corpus and on 26 targeted subjects, with no witness of a reachable difference — not a theorem.

## 3. (b) The trace as a LABEL — per-rule check

Machine check that applies to EVERY rule: `stepFn_sound : stepFn ctx s c ch = .ok (c', s', ch', tr) → Step ctx c s c' s' tr` (MachineSound:473) and `step_complete : Step ctx c s c' s' tr → ∃ ch ch', stepFn … = .ok (c', s', ch', tr)` (:820) — the SAME `tr` on both sides, no `∃ tr` anywhere in the 122 constructors (`grep -nE '∃ *tr|∀ tr' .tmp/Step.lean` → none); `stepFn_oblivious` (:5783) makes the label stream-independent; `stepMulti_sound : … → StepM ctx m m' ev.trace` / `stepM_complete : … ∧ ev.trace = tr` (MultiSound:1183/1329). So for every rule the label equals `stepFn`'s emission in `stepFn`'s order, by kernel-checked proof. Census of `Machine.lean:4510-5304`: 122 constructors; 94 conclusions end in `[]`; 28 carry a label variable fixed by a premise. The labelled family and how the label is determined:

| rule (Machine.lean `Step`) | label fixed by | shape |
|---|---|---|
| `evalVar` | `Mem.loadFor ctx s loc (projChainTarget ctx s k loc) = .ok (v, tr)` | one narrowed read |
| `evalStrictNullary`, `strictApply` | `toResult (applyStrictOp …) = .ok r` then `deliver s k (fun (out, s', tr) => …) r = (c', s', tr)` | helper's trace; panic ⇒ `[]` + pre-store |
| `stmtOpShiftTarget`, `stmtOpApply` | `applyStmtOp ctx s ch …` through `deliver` | idem (choice `ch` quantified; the label is stream-independent — `applyStmtOpCore_trace` covered append's two paths) |
| `callImmediate`, `callArgsDoneEnter`, `callValCalleeEnter`, `callValArgsEnter`, `frameDeferFall`, `frameDeferReturn`, `panicFrameDefer` | `enterFramePick … = .ok (r, ch')` then `deliver … (fun (func, frameEnv, _, s', tr) => …) r` | the dispatch read (`dynamicDispatch?`), panic ⇒ `[]` |
| `frameReturnTargets`, `frameFallTargets` | `loadResults` (frame exit) | result-cell reads |
| `mapRangeStart`, `mapIterNext`, `mapIterDone`, `mapIterStop` | `mapRangeStartSets`/`mapIterCandidates` | map-object reads |
| `rhsStores`, `storeStep` | `applyRhsOp` / `storeTarget` through `deliver` | writes |
| `chanStApply`, `syncStApply`, `atomicStApply` | `deliver s k (fun (c', s', _) => (c', s', [])) r` | **always `[]`** — payload/sync/atomic traffic is S2c's; the `.wgAdd` negative-counter outcome (a `.panicking` config with the sync cell written, by design) is a sync-WORD write, not `.data` |
| `selectApply` | `applySelect` through `deliver`; `stepFn_selectApply_inv` adds `tr = []` | `[]` |
| `unseqRunLoad` (+ the `unseq*` helpers) | `unseqLoad`/`unseqAtoms`/`unseqTargetPlan` | binder writes emit, binder loads peek (disclosed) |
| the 94 pure rules | — | `[]` |

Panic-delivery convention checked against the footprint-lie worry: `deliverS` (StepFn.lean:58-64) returns **the PRE-apply store `s`** with `[]` — so whenever the label is `[]` because a panic was delivered, memory is UNCHANGED (the W arms' writes are rolled back). Scratch `scratch-warm-results.txt`: the two REACHABLE W arms (`*p = make(map…)`, `*p = make(chan…)` into a nil pointer) panic on both binaries and Go (1, 2, and a following allocation is undisturbed: 6). No footprint lie. The pool's spawn label is the child's entry read (`spawnStep`, Multi.lean:586-608; `spawnStep_trace` at `6bb1930d`); the pool's select interception delivers `[]` (Multi.lean stepThread). `raceUpdate` (Multi.lean:1855) folds `ev.trace` at the SAME two positions the old fold read the table (`:1874` spawn, `:2126` the `privateStep` fall-through; main `:1863/:2110-2112`), the chan/sync/atomic apply arms record through their registry arms unchanged.

## 4. (c) `accesses_eq_stepAccesses` — statement, hypotheses, what guards the trace now

`git show 6bb1930d:GoLean/GoCore/AccessTableEq.lean` (1,496 lines, sha256 `6075b63f…`, 71 top-level decls): `theorem accesses_eq_stepAccesses {c s c' s' tr} (h : Step ctx c s c' s' tr) : tr = tableTrace (stepAccesses ctx s c) ∨ (tr = [] ∧ c'.isPanicking = true)` (line 1229) — per step, per configuration, **no hypothesis beyond `Step`** (no `StateWf`, no `HeapNormal`, no program well-formedness): stronger than the corpus needs, EXACT equality (order included) on the non-panicking successor, not «up to permutation». Corollary `_of_not_panicking` (:1466); `spawnStep_trace` (:1476) for the child's `dispatchAccesses`. Its ONE gap in the prose is F4 (true by inspection). After deletion the trusted side is the TRACE; what guards it is the labelled coherence (§3) + `HeapNormal`/`StateWf` preservation + the `Mem.*` definitions — and NOTHING mechanical about which call sites emit (F7). Plainly: the emit/peek discipline is now «by construction», documented (`Ops.lean` module docstring), and reviewed; it is not checked.

## 5. (d) The two tightenings

- `sortSlice` → `Mem.loadSlice` + structural `intElems` (Machine.lean diff): the old `for` loop refused at the first non-int AS IT LOADED; the new form loads ALL elements (`validateSlice` first) then checks. The only observable difference is refusal ORDER under a header/backing inconsistency (`validateSlice` checks `len ≤ cap` only) — no `StateWf` conjunct excludes it, no well-formed program reaches it. The op is DEAD: `tools/nativefrontend/stdlibsource.go:86` — «the sortSlice MACHINE OP intercept retired»; no Go program lowers to it, so no differential witness is possible. Semantics-preserving on well-formed programs as claimed; deletion owed (A11).
- `len`/`cap` of a pointer-to-array: `some (.pointer (.array n _))` now requires `v ∈ {.addr _, .nil}`, else `stuck "len of a pointer-to-array expected a pointer operand, got …"`. Scratch #11 (`lenCapPtrArr`, nil and non-nil pointers) SAME = 7755 = Go. A non-pointer value under a pointer-to-array static type is ill-typed; fail-closed doctrine, no reachable difference constructed.

## 6. (e) The fold's corner

`scratch-deferrecv-main.go` (4 subjects): `defer s[i].M()` / `defer s[i].P()` with `i` out of range panic AT DEFER TIME (receiver evaluation) on both binaries and Go (1, 2); an in-range element pointer formed at defer time, slice then shrunk, unwinding runs the deferred method fine (100, 103) — the address was bounds-checked at formation, exactly the handoff's argument. Not reachable from these shapes; the corner stands as recorded (and the label's account — nothing — is the honest one).

## 7. (f) The deletion

`git grep -nE '\b(stepAccesses|strictOpAccesses|stmtOpAccesses|storeTargetAccess|dispatchAccesses|deferEntryAccesses|unseqRunAccesses|sliceElemLocs|mapAccess|targetWrite|RaceAccess|tableTrace|AccessTableEq)\b' -- GoLean Tests Main.lean scripts tools lakefile.toml`: 11 hits, ALL in comments/docstrings (Race.lean:33-37 the tombstone header, NPDRF.lean:140/420/435 obstruction prose, Ops.lean:1680/2995/3042 docstrings); `RaceState.access(es)`, `arraySet`, `StructFields.set`: comment mentions only. `NPDRF.lean`'s live definitions `footprintsConflict`/`RacyFine` (:421/:438) are over `AccessTrace` labels via `StepE`; `NPDRFReduction` carries `@[deprecated … (since := "2026-09-18")]` (:477), 0 uses. The tracer's tombstone (`ChoiceTrace.lean:194-196`) names the two 0-mismatch runs. `Race.lean` is 956 lines (header replaced; U5 verbatim). Tombstones accurate.

## 8. (g) Coherence and totality

Covered in §0/§3/§4: labelled coherence in both directions with the SAME label; `step_preserves_wf` over `MachineWf` (`StateWf` now `∧ HeapNormal`); `MultiWf ctx m` restated (context re-read for `HeapNormal`); no new frame data (C3's). New recursions: `Loc.rootPath` (on `Loc`), `fieldIdxFrom` (fuel), `Ty.stepDown` (bound), `writeAt` (path list), `Mem.loadElems`/`storeElems` (Nat/list), `intElems` (list), `HeapNormal` via `List.all` — all structural; `Array.modifyM`/`.modify` are library. Core audit: classical trio only (§0).

## 9. (h) The spike

`spikes/c1-frame/Frame.lean` 914 lines, sha256 `2a510942…` (matches). (a) `arraySet_comm` (:546), `fieldModify_comm` (:570), `Array.modify_comm` (:510) — as claimed. (b) `isNormalForTyTy_array_set` (:604), `isNormalForTyAt_struct_set` (:651) — one `.index`/one `.field` depth. (c) `F1`/`F2` (:675/:683) stated with the chartered hypothesis `ShadowKey.overlap (.data l) (.data m) = false`; `F1Canon`/`F2Canon` (:692/:699) with `(rootPath l).1 ≠ (rootPath m).1 ∨ pathsDisjoint …`; **`f1_canon : F1Canon ctx` proved** (:843). Precisely: the charter wanted F1 under the detector's own relation (`ShadowKey.overlap = false`); `f1_canon` proves it under the CANONICAL relation (field steps reduced to names, typeIds erased). The difference is exactly BUG-111's class: two structurally distinct keys naming one word are `overlap = false` yet NOT canonically disjoint, so F1-as-chartered fails there and F1Canon says nothing about them. `F2`/`F2Canon` are stated only (the charter asked for F1 at depth ≤ 2; F1Canon is proved at every depth — stronger on the proved side, weaker on the relation). The stub `stubStore` (:249) is the S1 shape (`leafTy` + `normalizeValueForTy` + `writeAt` + one `updateCell`); the real S1 `storeLoc` normalizes at `Ty.stepDown`'s `(type, bound)` instead — the frame law on the REAL `storeLoc` is owed (handoff §6a), not ported. The refutation of F1 is by `#eval` (findings 1/3), and F10 confirms it end-to-end with gc.

## 10. (i) Benchmarks

Two measurements: the lane's runner (`run-probes.py --plan full --only empty,append_grow,write_fixed,scalar,alloc_new,heap_then_scalar,read_fixed`, 3 runs, medians, net of the empty probe) on both binaries — the candidate's pass ran UNDER my own concurrent jobs (detector-soundness ×6, a tracer ×6, the S2a build) and is inflated; main's pass ran later at lower load — and an INTERLEAVED re-timing at load ≈ 1 (`bench-interleaved-clean.txt`: 5 reps alternating main/cand per point, medians of wall s). The interleaved numbers are the ones to read for the ≤ 10 % targets.

| probe / point | BEFORE (lane, main) | this audit main (full/interleaved) | this audit cand (full, loaded / interleaved) | target | verdict |
|---|---:|---:|---:|---|---|
| `append_grow(4000)` net | 30.42 s | 31.07 / **29.45 s** | 0.378 / **0.31 s** | < 2 s | **MET** (95×) |
| `append_grow` ×2 ratios (250→4000) | ×5.0 ×6.2 ×6.5 ×6.7 | — | ×1.6 ×3.5 ×2.1 ×2.8 | ≤ 2.2 | **MISSED** (as the lane reported; cost B) |
| `write_fixed(m,100)` net, m = 10/100/1k/3k/10k | 2.6 ms → 10.8 s | 2.6/4.7/119/988/**10,808 ms** | 5/2/2.5/5.5/**11 ms** (noise floor) | flat within 2× | **MET** (the slope is gone; 100 writes sit in the 20 ms startup noise) |
| `write_fixed(10,10000)` wall | — | **0.17 s** | **0.16 s** | (per-write linearity) | equal |
| `write_fixed(10000,100)` wall | — | **10.65 s** | **0.02 s** | (cost A witness) | quadratic gone |
| `scalar(80000)` wall | 0.964 s net (246 ns/step) | **1.07 s** | 1.22 (loaded) / **1.05 s** | within 10 % | **MET** (−2 % interleaved; the +13 % was my load) |
| `read_fixed(10000,1000)` wall | 17.8 µs/read | **0.03 s** | 0.031 (loaded) / **0.03 s** | control | equal |
| `alloc_new(4000)` wall | 0.245 s | **0.27 s** | **0.27 s** | (S3) | unchanged |
| `alloc_new(32000)` net | 13.77 s | 13.85 s | 16.62 s (loaded) | (S3) | unchanged class — cost B unfixed, as claimed |
| (h) `heap_then_scalar(40000,20000) − (40000,0)` vs `(0,20000)` | 6.375 vs 0.237 s | 5.34 vs 0.272 s | 5.17 vs 0.286 s | (S3) | unchanged — cost B unfixed, as claimed |

## 11. (j) Trace-equality audit — reproduced on a subset

S2a binary (`d4c0c14d…`, both accounts live): `scripts/choice-trace-corpus --dump --jobs 6 --golean .tmp/golean-s2a` over 307 manifest ids (every 12th executable row, the 2 standing exclusions removed; `choice-trace-subset-ids.tsv`), 6 streams → 302 traced rows × 6 = **1,818 (row, stream) results; `traceMismatches` = 0 in every chunk, 0 rows non-zero** (`trace-audit-s2a-subset.txt`; statuses ok 1488 / panic 198 / unsupported 78 / deadlock 24 / race 18 / fatal 6 / stuck 6); its consumption dump `cmp` EXIT=0 vs main's on the same subset. The tracer compared MULTISETS (`traceMultiset` = sorted canonical keys, `7f7c721c:ChoiceTrace.lean:217`), not order. Does order matter for the detector? No: `RaceState.accessKeys` (Race.lean:431) checks-then-records each access against OTHER goroutines' epochs (unchanged within a step) and `ShadowCell.record` (:151) upserts per kind per goroutine, so a step's verdict and its post-step shadow are order-independent; the theorem's exact-order equality is stronger than the fold needs.

## 12. (k) Records

Gate tails (`gate-tail-{s0,s1-checkpoint,s1,s2a,s2b1,s2b2}.txt`): each shows `RESULT: FAIL` with exactly two red steps — `certificate provenance` (STALE on NPDRF.lean / Machine.lean / CLI.lean) and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`; the drift block is present each time — confirmed, all six. Choice-trace byte-identity reproduced on the 307-id subset: sorted dumps `cmp` EXIT=0, 2,690 records each side, sha256 `abb41cb7…` both (`choice-trace-subset-cmp.txt`). Handoff §5: every row has an alternative named (30 rows) — yes. BUG-111 entry: accurate (F10), fix PENDING [USER]. D8 marker text as recorded; 0 uses; 0 warnings. D10 as recorded. Evidence caps: PASS. Census (§4 of the handoff) spot-checked: table family 54/6/5 → 0 live mentions (§7 above); `deliverS` sites; `raceUpdate`'s `threads.size ≤ 1` early return is pre-existing (main :1848). Records defects: F1, F2, F3 (docstring), F4, F5, F6.

## 13. (l) Scope

No C3 (frame list untouched; `projChainTarget` MOVED Race→Machine, `recvFieldChain`/`wrapperForwardArg` MOVED Race→Ops as `dispatchLeaf` — motions, the wrapper-hop narrowing kept for P), no C4 (no `free`, no reclamation event), no Stage C. Semantic changes beyond the two disclosed tightenings: `alloc` normalizes (D3, disclosed, gated), `mapDelete` of an absent key emits (disclosed), the unbound-root-under-path `.internal` (disclosed), and F3's interface-cell refusal (NOT disclosed). `MultiWf` regained `ctx` (disclosed).

## 14. What I did NOT check

- A full `scripts/ci --diff` (box-wide lock) — not needed: the six tracked tails were audited and the focused checks reproduce; the certified re-check (5a) is the train's.
- The whole-corpus choice trace (21,835 results) and the raft twin — a 307-id subset only (§11/§12); the twin's 1,100 s runs not repeated.
- Every one of the 60 theorems' bodies in the deleted file, and the ~2,800 changed lines of `StateWf.lean` — statements and the kernel/audit result only.
- The 28 labelled rules one by one beyond the ten shown in §3 — the kernel-checked coherence pair is the per-rule check.
- `F2`/`F2Canon` (stated only in the spike, as the charter allowed).
- A Go witness of a non-normal value reaching `Store.alloc` (none constructed; not proven impossible).
- The detector-soundness gc side with the OFFICIAL runner (it cannot run until F2's fix); §1a is a patched-copy run.
