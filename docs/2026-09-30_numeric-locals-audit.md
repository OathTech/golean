# Audit of `core/numeric-locals-0930` at `a6df705f` (B6, window row 5: `VarId := Nat`)

[AGENT auditor, branch `review/numeric-locals-0930`, worktree `.claude/worktrees/audit-numeric-locals`]
2026-09-30. Candidate tip `a6df705f` (runtime commit `0fb43dcd`) over `131a7313`; `main` is `90df0fe1`
(records-only since `131a7313`; runtime sources identical). Under the [USER]'s every-merge-audited rule
(relayed). The candidate and `main` were not edited; no merge, no push. Evidence (small):
`docs/evidence/2026-09-30_numeric-locals-audit/` — `ab-corpus.txt`, `ab-enum.txt`, `probes.tsv`,
`mutants.tsv`, `wire-diffs.txt`, `ci-slow-tail.txt`. Scratch under the worktree's `.tmp/` (deleted at the end).

## Verdict: MERGE-CLEAN

The lane's claim — a pure renaming of every local position from `String` to `VarId := Nat` with ZERO behaviour
change — holds on the auditor's own re-derivation: main's frontend+binary and the candidate's were built
independently and every corpus row was lowered and run through both; the outputs and exit codes of all 3791
manifest rows are byte-identical (the one differing byte string is the wire's absolute PATH inside the
pre-existing BUG-078 refusal), the enumerated observation sets and enumerator statistics of 686
argv-identical enumerations and of all 386 non-strict rows re-enumerated with their own lane parameters
(incl. the certified slow-tier row at its claim's argv) are identical, 21 auditor-written scoping programs
covering the logic team's §4 B6 conditions run identically on both sides and agree with `go run`, and every
core theorem statement is unchanged except for `String → VarId` at binder positions. Findings are LOW and
TRIVIAL — record and design-scope notes and one defence-in-depth remark — none blocking. D1–D6 are assessed
below as PENDING [USER] items; this audit decides none of them.

## Findings (by severity; witnesses in the evidence files)

**F1 — LOW (design scope). «Checked table» is one-directional: the decoder certifies the TREE against the
table, not the table's per-object story.** Witnesses (`mutants.tsv`, all decode and run identically to the
unmutated wire): M1/M12 — an inner `x := …` DECLARE carrying the OUTER `x`'s declaration id (with its
references following) passes c1–c5: declaration identity per go/types object is not enforced (it cannot be,
under D1's «one id, several declaration sites» for the per-iteration loop copy); M6 — a body local's table
kind forged to `recv` passes (c2 checks kinds for SIGNATURE entries only); M13 — when an entry carries `wire`
(1213 of the 18556 corpus table entries: 1198 capture pointers, 15 shadow renames; 60 of the twin's 2879),
its `name` — Go's identifier, the customer's reconstruction key — is compared with nothing; M14 — `pos` is
unverifiable by construction; M16 — an unused table entry passes (coverage is tree ⊆ table only). None of
these changes semantics: the renaming certificate (c3/c4: the decoder's lexical walk and the wire agree at
every reference) holds regardless of what the table says about objects. But the design's D3/D5 sentence
«the checked metadata lets a client reconstruct bindings after renumbering» should be scoped in the
design/handoff/changelog to what is actually checked (index range, `wire`-or-`name` spelling agreement at
each declaration and reference, scope, resolver agreement, signature kinds and distinctness), with the
unchecked fields named (`name` behind `wire`, `pos`, body-local kinds, unused entries, per-object identity).
Cheap strengthenings, if the [USER] wants them, PENDING: (i) compare `name` with the base spelling when `wire`
is set (`x$cap` → `x`, `x$shadowN` → `x`); (ii) require every table entry to be named by the tree (table ⊆
tree); (iii) fold the signature-kind check into the core predicate `Func.localsOk` so a consumer's `localsOk`
premise yields kinds (today c2 is decoder-only; `localsOk` gives only `< size` and signature distinctness).

**F2 — LOW (design claim overstated). D6: «the decoder's checks make the unbound cases unreachable for a
decoded program» is false for `$`-temporaries.** Witness M15: a `$`-spelled reference that no declaration
introduced (`$ghost`) decodes (D2 interns every `$` spelling on sight, no scope check) and reaches the
machine's `stuck "unbound GoCore variable address: 5"`; on `main` the same wire reaches the same refusal
with the spelling. No behaviour change; the sentence should read «for source locals».

**F3 — LOW (defence in depth moved out of the machine; recorded PENDING under D6).** Retiring `b4` and
`mBareTarget` removes the MACHINE-level audit-F3 guard: a hand-built graph whose binder cell shadows a
source local is no longer refused by `UnseqGraph.wellFormed?`; only the decoder's `binder` spelling test
remains, which a Lean-level program bypasses. `mUnknownSlot`'s retarget moves a refusal from ENTER (static,
before any occurrence runs) to the read (`stuck` after earlier occurrences may have run their effects).
Both are honestly recorded and the wire mutants `mut-nondollar`/`mut-unknown-slot` keep their named
refusals (verified; `mutants.tsv` W1–W4 show the same one-edit mutant refused by name on both sides — the
`wellFormed?` texts for guard test/completion slots now print the interned id, e.g. `tests '7'`). An
alternative that keeps the F3 intent at the machine without spellings (assessment only): a total check at
`unseq` ENTER that no cell id is already bound in `env` — unreachable for decoded programs (temps are
interned past the source ids) and restoring the hand-built protection. For the [USER] to weigh.

**F4 — TRIVIAL (records).** The changelog's D6 row lists the refusal texts that now print a number
(`unbound GoCore variable address`, `unbound GoCore result variable`, `unseq: unbound target operand`, the
graph validator's binder texts); the last item covers every `wellFormed?` message that quotes a binder
(`result binder`, `cell … produced by no occurrence`, `sort mismatch`, `guard … tests/completion`, `store
target/value`) and the two `Machine.lean` texts `binder cell '{bind}' is not declared` / `target binder
'{tgt}' has not been produced`. None appears in any baseline row (`native-full.tsv`, `negative-full.tsv`:
zero hits; the one grep hit is a header comment). Fine as written; a parenthesis naming the family would
save the next reader a grep.

**F5 — TRIVIAL (records).** `Tests/GoCoreEval.lean`'s stray-read check gained a conjunct `v == vid "t"`
(the read variable's id is now asserted) — a test strengthening the handoff does not mention. Harmless.

## What was verified, by the brief's attack list

1. **Pure renaming, independently** (`ab-corpus.txt`, `ab-enum.txt`). Main's tree from `git archive
   131a7313` with its own `go build` of `tools/nativefrontend` and the primary's `golean` (lake judged it
   current against those sources; sha256 `8e042f19…`); the candidate's `.lake` warmed from the lane worktree
   after `diff -r` on `GoLean/ Tests/ Main.lean lake-manifest.json lean-toolchain` (identical) and lake-verified
   (`302956fc…`). All 1368 fixture dirs lowered by both frontends (exit codes and stderr identical per dir; 24
   dirs refuse on both sides — the pre-existing 34 rows). All 3791 rows run through both binaries: one
   differing file = the BUG-078 path string. Enumeration: 686 rows (all 386 non-strict + 300 strict) at one
   argv → identical `.obs`/`.stats`/`.rc`; then all 386 non-strict rows with their own `width/sites/cap/work/
   engine/backedge/nonterm/statuses` (the certified row at its claim's argv, work 60 000 000, engine dedup)
   → see `ab-enum.txt`. The certified row's wire: `dc232a8c…` (= the record's `claim.wire_sha256`) →
   `f448d579…`, exactly the lane's numbers.
2. **The logic team's conditions** (`probes.tsv`): 21 programs — recursion with re-entered blocks, Go 1.22
   per-iteration loop variables with `&i` and closures escaping, range-variable capture, goroutine capture
   (race on both sides), shadowing across if-init/switch/type-switch/select/goto/nested blocks and inside an
   `unseq` sweep, same-block `:=` reuse of `err`, named results (incl. written by a deferred closure), unnamed
   and blank parameters and receivers, method values/expressions, nested closures re-capturing an outer
   capture with a parameter shadowing a captured name, generics stencils, embedded promotion, labels vs
   variables, goto hoists, declaration forms (var groups, blank results, locals named `nil`/`true`, a const
   shadowing a local). Every one: main = candidate byte-identical and = `go run`. «Numeric ids are not an
   API promise» is stated in `Syntax.lean`'s docstring, `locals.go`, the changelog row and the design.
3. **D1's certificate** (`mutants.tsv`): 24 auditor mutants beyond the gate's 11 — swapped/forged ids
   (M4, M4b, M9, M11), a result slot re-pointed at a parameter (M3: refused as a signature binding an id
   twice / wrong kind), temp/user collisions both ways (M5, M5b), a truncated table (M7), v2-labelled and
   stripped wires (M8a–c), malformed indices (M10 ×5: negative, string, float, null, bool) — each refused BY
   NAME with the path. The predicted-to-pass mutants (M1, M2, M6, M12, M13, M14, M16) passed: F1. Legal edge
   cases (blank identifiers, `_` params, generics, receivers, labels, goto) decode: the probes.
4. **D2/D6** (`mutants.tsv` W1–W4): the two checks that left `wellFormed?` refuse the same one-edit mutants
   on both sides (v2 fixture on main, v3 fixture on the candidate); no mutant was found that main refused
   at decode and the candidate lets through to the machine. The three `Tests/UnseqScheduler.lean` rows: F3.
5. **Observable spellings.** No `print`/panic/race text embeds a local's spelling on either side; the
   refusal texts that do (F4's family) appear in no baseline row; the whole-corpus run A/B (item 1) is the
   direct check that no observation moved. The 49 respelled unnamed params/receivers (`""` → `$recv`/`$p{i}`)
   are env keys never referenced — confirmed by the run A/B and by the twin diff (the ONLY residual).
6. **Coherence/totality.** A mechanical classification of every changed line under `GoLean/GoCore/`
   (`git diff -U0`, `+` lines with `VarId → String` compared against the `-` lines): every non-additive
   change is the renaming; 22 theorem statements changed ONLY in a binder's type (`assigneeListSup_vars`,
   `LocalEnv.declare_locSup`, `LocalEnv.lookup_locSup`, `Scope.lookup_locSup`, `stepFn_mapIter_{done,
   ok_any,pick,stop}`, `unseq{Alloc,Invoke,Recv,Wide}Stmt_locSup`, `unseqCellLoc_locSup`,
   `unseqLoad_{commit_noPanic,inv_ok,inv_panic,plan_commitOk,plan_tame,pres}`, `unseqLookupTarget_strict`,
   `unseqStorePlan_{locSup,strict}`); `namesDistinct` generalized to `{α} [BEq α]`; `Func.eqbF` gains the
   table conjunct with its soundness. `ExecutionStatement.lean`, `Prefix.lean`, `PrefixFacts.lean`,
   `Trace.lean`, `ProgramTrace.lean`, `Ops.lean`, `MachineEqb.lean`, `CLI.lean`, both baselines,
   `baselines/certified/`, `scripts/ci`, `scripts/check-core-audit`, `tools/core-audit.py`: UNCHANGED.
   `scripts/check-core-audit`: PASS, 153 required theorems present. No `sorry`/`native_decide`/`axiom` under
   `GoLean/`; no `partial` under `GoLean/GoCore/`. The test-file changes are the `vid` wrapping, `v2 → v3`
   strings, `"locals": []` on hand-built wires, the `vid` helpers and F3's three rows (mechanically
   classified). Elaboration spot-check (StepFn/Machine/BridgeSet on both trees): within noise of the lane's
   table.
7. **Name-table interface.** Rows 108–125 pin what request 3 asked: the types (`VarId = Nat`; `Param.id`,
   `Expr.var/ref`, `Assignee.var` numeric; `Scope`; `LocalName`/`LocalKind`/`Func.locals`/`localName?`),
   `localsOk` with `localsOk_covers` («spellings retained» = every named id has an entry) and
   `localsOk_sigDistinct`, the env laws, and the slot lemmas (`bindParams_lookup`, `allocDecls_lookup`,
   `enterFrame_lookup_arg/_result`: argument `i` at `.base ⟨s.heap.size + i⟩`, result `j` after the
   arguments, under the distinctness premise). Rows 1–107 are byte-identical (namespace body compared). A
   mutated row 122 (`+ i` → `+ i + 1`) fails `lake build GoLean.GoCore.BridgeSet` with a type mismatch;
   restored. Caveat for the customer: «table lookup agrees with the activation's slot» is agreement BY INDEX
   (`localName? (args[i].id)` exists by `covers`; its KIND is a decoder check, not a core fact — F1 (iii)).
8. **Wire v3 / twin** (`wire-diffs.txt`). Reproduced with the auditor's frontends: main's emit = the OLD pin
   byte-for-byte, the candidate's emit = the NEW pin byte-for-byte; key-by-key after stripping the B6 fields:
   +12641 `local`, +60 `keyLocal`, +66 `valLocal`, 924 tables / 2879 entries, exactly 49 residual respellings
   (33 `$recv`, 11 `$p0`, 5 `$p1`) and nothing else — the re-pin reason is accurate to the digit. The
   certified row: +51 `local`, +1 `valLocal`, 8 tables / 18 entries, zero residual.
9. **Gate.** See `ci-slow-tail.txt` and the section below.

## D1–D6, assessed as PENDING [USER] items (not decided here)

- **D1 (per-object declaration ids from go/types, cross-checked by the decoder's lexical walk).** Sound: the
  certificate is exactly «two resolvers agree at every reference», and the run A/B is the direct evidence
  that the id walk and the spelling walk pick the same binding on the whole corpus. The alternatives are
  honestly stated; note that alternative (b) (decoder-only per-declaration split) would have made
  declaration identity CHECKABLE (F1 M1/M12) at the price of the cross-check — a real trade the [USER] may
  want to see named as such.
- **D2 (`$`-temporaries interned by the decoder, per spelling per function).** Sound and a bijection with
  today's shadowing; F2 is a wording fix only.
- **D3 (`Func.locals : Array LocalName` with `pos`).** Sound as carried data (the machine never reads it —
  grep-verified: no `.locals`/`localName?` in `Machine`/`StepFn`/`Ops`/`Multi*`/`State`). «Checked» needs
  the scope of F1; `pos` is basename-only (fine within a function).
- **D4 (schema v3; `local`/`keyLocal`/`valLocal` + `locals`; twin re-pin).** Sound; reason reproduced (item 8).
- **D5 (c1–c5).** Accurate as a list of what IS checked; F1 lists what is not. c5's `localsOk` is the right
  total core predicate for a consumer; (iii) above would make it carry kinds.
- **D6 (refusal texts print numbers; two spelling checks moved to the decoder; three test rows).** Sound;
  F3 names the one real loss (machine-side defence for hand-built graphs) and an alternative.

## Gate (item 9)

`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `a6df705f`, under the box-wide lock (taken by atomic
`mkdir`, owner file, trap-released; never taken over), in this worktree with the audit's untracked note and
evidence files present (the gate's `git_dirty=true` note; no runtime file differs from the tip): **EXIT 1,
`RESULT: FAIL` on exactly the 5a pair** — `certificate provenance` (STALE: changed dependency
`build/files/GoLean/GoCore.lean`, the train's 5a business) and `baseline diff` with the ONE drift line
`imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the certified
slow-tier row's wire-hash refusal, the train's step). `differential coverage summary: cases=3791 pass=3553
fail=238` = the lane's numbers = the pin's 3554/237 with that row. Every other step ok: escape-hatch preflight
and addendum, engine-isolation, core build warning-free, core totality audit (153 required), declaration and
wire boundary (the 11 B6 controls + the v2 control), method identity, unseq scheduler and wire (56 mutants +
the `build.py --check` re-derivation), frontend pins (twin = the re-pinned bytes), frontend/lowerdiag/harness
Go tests, eval tests (298 ok), negative baseline (394, no regression), evidence-size gate, AGENTS.md alias.
`baselines/native-full.tsv` unchanged. Wall 1051 s. Tail: `ci-slow-tail.txt`. Reconciler (report-only): the
C9 STALE line above and the pre-existing C13 doc-version note.

## Not verified / limits

- The lane's whole-corpus CHOICE-TRACE comparison was not re-run; the auditor's run A/B (every row's
  observation and exit code) and enumeration A/B (every non-strict row's set and statistics) are the
  independent evidence of the same claim by a different instrument.
- Elaboration was spot-checked on three modules only; the lane's seven-module A/B table is taken as reported.
- Probes were checked against `go run` (no `-race` samples); the machine's race verdict on
  `goroutine-capture` is identical on both sides, which is what this audit needed.
- No attempt was made to construct a Go program on which the machine's runtime scoping differs from Go's
  lexical scoping (the only way the id walk and the spelling walk could diverge); the corpus and the 21
  probes found none.

## Re-verification (`f11dad1f`, 2026-09-30)

[AGENT auditor] The fix round landed on `core/numeric-locals-0930` at `f11dad1f` (rebased onto `main` `90df0fe1`;
the first round's commits are now `79b48a2e`/`8a383bae`; snapshot `refs/snapshots/b6-fix/pre-rebase` = `a6df705f`).
D1–D6 RATIFIED ([USER] Mike 2026-09-30, verbatim, relayed: «Agree, go ahead and fix, agree on all 6»). This
branch was rebased onto `f11dad1f` (snapshot `refs/snapshots/audit-b6/pre-rebase`); `.lake` warmed from the lane
worktree after a `diff -r` of the Lean sources (identical; binary sha256 `ce232262…`, lake-verified).
`tools/nativefrontend` is unchanged since `79b48a2e`, so the twin pin and the certified row's wire are the first
round's. Evidence: `reverify-probes.tsv`, `reverify-mutants.tsv`, `reverify-corpus.txt`, `reverify-ci-diff-tail.txt`.

### REVISED VERDICT: MERGE-CLEAN

Every fix-round claim re-derived; the two attacks the coordinator asked for (F1(b) refusing a legal program; F3
refusing a legal decoded program the corpus lacks) produced no witness through the real frontend; the corpus
A/B and the enumeration A/B against `main` are identical again. Residual notes are TRIVIAL (assessment only).

### The claims, one by one

- **F1 (a) `wire` base spelling.** `decodeLocalsTable` refuses a `wire` whose base (before the first `$`) is not
  `name`, or that equals `name` — my M13 and two new variants (`P-wire-base-mismatch`, `P-wire-equals-name`)
  refuse by name; a `wire` renamed while the nodes still spell the base falls to c1 (`P-wire-renamed-but-nodes-
  spell-x`). Every frontend `wire` is `x$cap` / `x$shadowN` (base = `obj.Name()`), so no legal wire trips it:
  the corpus A/B below.
- **F1 (b) table ⊆ tree (`Func.tableNamed`).** My M1/M12 (a declare re-pointed at an in-scope same-spelling
  id — caught as the orphaned inner entry) and M16 refuse by name. **The attack**: does it refuse a legal
  program? Go itself refuses an unused local (`declared and not used`), so the candidates are the objects the
  frontend numbers without a surviving node: unused named parameters/results/receivers, blank `_`
  parameters/receivers, only-assigned parameters, locals used only inside a closure, type-switch binders used
  in one clause of three (and an unbound type switch), write-only locals (`w = n; _ = w`), goto-hoisted
  locals, generic stencils incl. a bound generic method value, every ADMITTED sync/atomic type's stubs
  (`Mutex`/`RWMutex`/`WaitGroup`/`Once`, `atomic.Int32/Int64/Uint32/Uint64/Uintptr` — the `forceParamID`
  path that drops a parameter's index), the `fmt` shim lifts (capture tables from `golean-stdlib-shims.go`),
  method values and a deferred closure with an argument — 11 probes (`reverify-probes.tsv`): every one decodes
  and runs IDENTICALLY to `main` and equals `go run`; the one frontend refusal (`atomic.Bool`/`Pointer`) is the
  same text on both sides. Corpus: 3791 rows re-lowered and re-run, zero B6/F1/F3 refusal texts, one differing
  byte string (the BUG-078 wire path). Signature ids are in `Func.ids` by construction, so unused
  params/results/receivers can never trip it; the only frontend path that mints an entry and then drops its
  node (`syncStubBody`'s forced `$a{i}`) empties the table when no parameter keeps an index — the probe covers
  it. `$lit` interning is now lazy (`targetBaseExpr` in `LowerM`); `build.py` prunes and renumbers orphaned
  envelope entries (none were, per the lane; the 141 fixtures rebuild byte-identical in the gate).
- **F1 (c) kinds in the core predicate.** `localsOk := tableCovers && tableNamed && sigDistinct && argKinds &&
  resultKinds && recvFirst && bodyKinds`, refused part by part with the index and kind named; M6 (a body local
  as `recv`), `P-result-kind-capture`, `P-param-kind-local` refuse. Lemmas `localsOk_named`, `_argKind`,
  `_resultKind`, `_recvFirst`, `_bodyKind` (+ `localsOk_parts`, `kindOf?`); BridgeSet row 116 re-pinned with
  three part equations, rows 126–132 added (132 = the `unseqEnter` rule with its new premise); rows 1–107
  byte-identical to `131a7313`; mutating rows 126 and 132 fails the build with two type mismatches; the core
  audit's required list 153 → 158 (`check-core-audit` PASS).
- **F1 `pos`.** FORMAT checked (`basename.go:line:col`, positive decimals, bare `.go` basename): five malformed
  variants refuse by name (`P-pos-*`); a well-formed forged position decodes (M14, `P-pos-ok-other`) — content
  unverifiable at the boundary, stated in D3/D5 as such. Accurate.
- **F2.** D6's wording now says «for SOURCE locals»; M15 (an undeclared `$`-temporary) decodes and refuses at the
  machine (`unbound GoCore variable address: 5`), as on `main`. Accurate.
- **F3 `unseqEntryCheck?`.** A second premise of `Step.unseqEnter` (no binder cell or target binder already
  bound in the enclosing environment; every mentioned slot a cell or a bound local), consulted by
  `stepUnseqEnter` before `allocDecls`; `stepUnseqEnter_sound`/`_stream`, `step_complete`,
  `step_complete_any_wf_aux` and `StateWf`'s case re-proved with the premise; `b4`, `mBareTarget` (its target
  binder now the source local `x`) and `mUnknownSlot` refused at ENTER by name. **The attack**: a legal decoded
  program the premise refuses would need a binder still bound when the sweep is entered — a sweep re-executed
  in the SAME scope — or a mentioned slot unbound at entry. Probes through the real frontend: two sweeps in one
  block (binders are `$u{tmpSeq}`/`$t{tmpSeq}` from a program-wide monotonic counter, so distinct), a sweep at
  goto-label level re-executed three times and a goto decl-region (the goto lowering's segments are blocks: a
  fresh scope per pass), sweeps in a `for` cond/post/body with `continue`, in a `select` loop, in
  `switch`/`fallthrough`/labelled `continue`, in range loops, in a closure re-capturing the same names, in a
  deferred closure with recursion — 9 probes, all IDENTICAL to `main` and equal to `go run`; the corpus A/B
  runs 3791 rows with zero entry-check refusals (the lane's «0 of 1354 decoded wires» reproduced by a different
  instrument). The domain narrowing is real but confined to HAND-BUILT graphs (K2's second sweep took suffix
  `2`) and is recorded in the handoff. Nested graphs are the decoder's Stage C refusal on both sides.
- **F4/F5.** The changelog's D6 row names the binder-quoting family and the two `Machine.lean` texts; F5 is
  recorded in the handoff. Accurate.
- **Gates.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `f11dad1f`, under the box-wide lock
  (atomic `mkdir`, owner file, trap-released, never taken over), with this audit's untracked/modified records
  in the tree (the gate's `git_dirty` note; no runtime file differs from the tip): **EXIT 1, `RESULT: FAIL` on
  exactly the 5a pair** — `certificate provenance` STALE and the ONE drift line `imported-goose/channel/
  google-search baseline[PASS/membership] -> now[FAIL/membership]` — `cases=3791 pass=3553 fail=238` = the pin
  with that row; `baselines/native-full.tsv` unchanged; every other step ok: core totality audit **158**
  required theorems, wire boundary **16 B6 controls**, unseq scheduler (the three re-pointed rows at ENTER)
  and unseq wire (56 mutants; fixture re-derivation), frontend pins (twin = `8a158eff…`), eval tests 298,
  negative baseline 394, escape hatches, engine isolation, evidence size. Wall 857 s. Tail:
  `reverify-ci-diff-tail.txt`. Enumeration A/B against `main` on the fix-round binary: all 386 non-strict rows
  with their own lane params identical (1289 observation lines per side; the certified row's 6 members hash
  to the record's `e40ba07d…`); corpus A/B: `reverify-corpus.txt`.

### Residual (TRIVIAL, assessment — no action required)

- `argKinds` admits `recv | param | capture | temp` for ANY argument and `recvFirst` constrains position only:
  a plain function's first parameter may carry kind `recv` (`P-plain-func-param-as-recv` decodes; `Func` has no
  is-method bit) and a capture pointer's entry may claim `param` (`P-capture-param-as-param` decodes). A
  consumer reading kinds gets «one of these», not the exact role — the honest reading of rows 128–130.
- The scripts `.tmp/ab-*.sh`, `.tmp/probe3.sh`, `.tmp/mutants/make.py`, `.tmp/wirediff.py` and the probe
  sources are the audit's reproducible instruments; they stay under the ignored `.tmp/` (312 K), not tracked.
