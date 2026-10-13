# Refusal-cause pinning — design note (2026-10-12)

[AGENT] lane `docs/refusal-cause-design-1012`, release-readiness item 8
(`docs/2026-10-12_release-readiness.md`: «design note first, then a lane»);
gate-audit F9 (`docs/2026-09-05_project-gate-audit.md`, accepted 2026-09-05,
still open). Design only: no script, baseline or manifest changes here. The
baseline-format change this note recommends is the [USER]'s to approve (§5).

## 0. Summary

- The baseline pins a red's `(result, stage)`, never its cause. On main's
  recorded run: 239 FAIL rows; 191 at `frontend-export`, 33 at
  `lean-observation`. A crash, a timeout, or a different refusal at the same
  stage matches the baseline. A machine panic or stuck where gc runs `ok`
  (a wrong answer) also matches it on the 33 `lean-observation` rows. This
  happened once already: `strings/trimspace-repeat/repeat-bound-refused` was
  `Lean run KILLED (exit 134 … Stack overflow)` while the records called it a
  named refusal (item 9). The gate stayed green, and a reviewer found it.
- The negative lane runs no GoLean code at all. Measured today: the native
  frontend rejects all 394 negative programs (356 at `type-check:`, 37 at
  the parser, 1 at file selection). Nothing gates that.
- Recommendation ([AGENT]): **Option A**, a `cause` column in
  `baselines/native-full.tsv`. It holds a normalized key, derived from the
  detail the runner already records, and is compared by
  `coverage-baseline-diff`. Add to it **the negative frontend leg**: a
  negative row passes only if gc rejects it AND the frontend refuses it as a
  rejection (type-check, parse or file selection). It costs about 1.5
  sessions. The fast gate adds under 3 s, the `--diff` tier about 42 s
  serial (measured). Migration is one re-pin that adds the column; no result
  or stage moves.

## 1. The gap, measured on main today

**Source.** `artifacts/coverage/latest.tsv`, the recorded full run at
`eb177b39` (`latest.meta.tsv`: `git_dirty=false`, go1.26.5, 3953 cases).
Main's tip `d4be5dca` changes only records on top of `eb177b39`, so the run
is main's. `scripts/coverage-baseline-diff --full` against
`baselines/native-full.tsv`: «no regression: 3953 case(s)». The negative
record `negative-latest.tsv` is at the same commit: 394 cases, 394 PASS.
Scratch scripts are in this worktree's `.tmp/` (ephemeral).

### 1.1 FAIL rows by stage

| stage | FAIL rows | what the detail holds |
|---|---:|---|
| `frontend-export` | 191 | 34 export-time refusals (frontend exit 1, no wire: `native frontend: nativefrontend: …`) + 157 RUN-TIME quarantine stubs reached (the machine ran to a stub, `status:"unsupported"`, `frontend-quarantined: …`, reclassified to this stage at `scripts/diff-coverage:969`) |
| `lean-observation` | 33 | `expected status <s>, got {…"status":X…}`: X = `unsupported` 21, `race` 6, `stuck` 5, `error` 1; plus 1 variant-stream refusal (`channels/select-select/beside-loop`, landing on its `lean-observation\|differential` alternation) |
| `go-observation` | 10 | oracle-side: the harness could not read gc's abort (no hook ack ×5, invalid UTF-8 panic text ×3, ambiguous fatal ×1, race-with-output split ×1) |
| `differential` | 4 | `Lean=… Go=…` (2 latitude records, 2 BUG pins) |
| `confluent` | 1 | `goroutines/worker-pool/sum`: the enumerator's undeclared-`backedge` refusal |
| **total** | **239** | of 3953 rows (3714 PASS) |

Non-verdict rows today: **0**. No detail carries the runner's
`KILLED (exit …` or `TIMED OUT after` phrases. That is a statement about
this run, not a property the gate holds (§2b).

### 1.2 By cause family

`frontend-export` (191). Classified with `tools/lowerdiag classify` (the
`causes.tsv` table, first match in table order, which is the tool's
documented rule). **188 classify into 36 cause ids. 3 are UNCLASSIFIED**
(`builtins/print/refused/chan`, `generics/chan-type-arg/first`,
`spec-examples-decl/var-comma-ok-matrix/shadow-capture`). All three are
run-time stubs whose text is still wrapped in the observation JSON. They
would classify once the message is extracted first (§4 step 2). 40 texts
match more than one row, and first-match resolves them deterministically.
The largest families:

| cause id | rows | | cause id | rows |
|---|---:|---|---|---:|
| FR-15/complex | 30 | | FR-23/imported-generic-inst | 6 |
| FR-14/stdlib-package-unmodeled | 28 | | FR-18/alloc-short-circuit | 6 |
| FR-14/fmt-verb-matrix | 16 | | FR-11/goto-hoist | 5 |
| FR-13/anon-struct | 9 | | FR-1/go-of-builtin | 5 |
| FR-12/range-over-func | 9 | | (24 more ids) | ≤ 4 each |
| FR-7/tuple-iface-box | 8 | | | |
| out-of-language/unsafe, c-pin/print-builtin, FR-38/uintptr-identity | 6 each | | | |

The tool's templated KEY column (`$1` groups such as `os.Getenv`,
`reflect.TypeOf`) splits the same 191 rows into 59 distinct keys. Those keys
depend on fixture names and are finer than a cause (§3, decision D2).

`lean-observation` (33): 15 distinct machine messages in 13 families, with no table today. NaN-payload
float-bits ×7 (6 Float64bits + 1 Float32bits), data race (designed BUG-084 /
BUG-pinned) ×6, nil slice-base `stuck` ×5, select-with-select ×2,
float→int out-of-range ×2, slice→array L2b ×2, panic-while-printing ×2,
recovered runtime-error type ×2, init print ×1, init `go` ×1, imported-type
hashability ×1, array materialization budget (`error`) ×1, slice cap budget
×1.

### 1.3 Red-by-design vs. untriaged

Cross-tabulated against `docs/BUGS.md` `Cases:` lines and
`baselines/untriaged-ids`:

| ledger standing | fe-export | lean-obs | go-obs | diff | confl | total |
|---|---:|---:|---:|---:|---:|---:|
| `Expect: FAIL` entry (6 entries: BUG-084, 091, 093, 094, 100, 124) | 19 | 13 | 1 | – | – | **33** |
| open `Pinned-by: differential` entry | 1 | 6 | 9 | 2 | 1 | **19** |
| other BUGS entry (`Pinned-by: none`) | 9 | 2 | – | – | – | **11** |
| `untriaged-ids` (coverage 10 / latitude 4) | – | 12 | – | 2 | – | **14** |
| **no ledger at all** | **162** | – | – | – | – | **162** |

The 162 unledgered rows are all frontier refusals at `frontend-export`. The
only record that classifies them is `causes.tsv`/lowerdiag, and that
classification is diagnostic: no gate reads it against the corpus.
`check-bugs` counts only fidelity stages, so it never looks at them.

### 1.4 The negative corpus

`scripts/coverage-negative` (lines 203-212 at main) records PASS for a row
iff `go build` exits non-zero within `GO_TIMEOUT_SECONDS` (30 s) **and** its
combined output contains the manifest's `expected_substring`. **GoLean's side
asserts nothing.** The script never invokes the frontend, the decoder or the
machine. The baseline header has said so since 2026-08-31 (p2-fact claim 5).

Measured now ([AGENT], `.tmp/negfe.sh`, the frontend built from this tree).
The native frontend over the 394 negative directories:

| frontend outcome | rows |
|---|---:|
| exit 1, `type-check: …` (go/types rejection) | 356 |
| exit 1, go/parser rejection (`<file>:L:C: expected …`, `illegal rune literal`, …) | 37 |
| exit 1, `native frontend unsupported: file selection … found packages helper and main` (`imports/package-mismatch`, the BUG-108 boundary) | 1 |
| exit 0 (lowered a program gc rejects) | **0** |
| exit ≥ 2 (Go panic or signal) | **0** |

367 of the 394 frontend messages also contain gc's expected substring. The
27 misses are wording differences: go/parser vs. gc syntax errors, and
`label L declared and not used` vs. gc's `defined and not used`. So gc's
substring is the wrong thing to assert on GoLean's side. The class
(type-check / parse / file-selection) is the right one. Wall time: **41.8 s
serial** (0.106 s/row; go/types loads the standard library per row).

## 2. Failure classes the current pin cannot catch

Two facts shape every scenario. First, `coverage-baseline-diff` compares
`bres/bstage` against `$1/$4`. Second, `diff-coverage` reports every frontend
non-zero exit at `frontend-export` (`:857/:860/:863`): a timeout, a signal,
and the generic `native frontend: <output>` arm, which covers a Go `panic`
(exit 2) as well as a named refusal (exit 1). It reports every Lean
non-verdict at `lean-observation` (`:961`; the comment at `:948-955` keeps
that stage on purpose).

**(a) The refusal cause changes at the same stage.**
`multipkg/init-order-staticinit/seq` is pinned `FAIL/frontend-export` by the
BUG-061 guard (`staticinit-uncertain-order`, train 3). Suppose a later edit
to `tools/nativefrontend/staticinit.go` makes the classifier nil-deref on
some shape. The frontend dies with a Go panic, exit 2, and the runner writes
`native frontend: panic: runtime error …` at `frontend-export`. The baseline
matches, and so does `check-bugs`: BUG-061 is an open differential entry and
only `FAIL` is required (§2d). Or suppose a fixture edit makes `zq` hit
FR-14 before the guard runs. It is still `FAIL/frontend-export`, and nobody
sees that the BUG-061 guard no longer fires on its own witness. Honest
limit: if the guard regressed to LOWERING the program, the row would run,
reach `differential` (Lean 21 / Go 12) and the stage pin WOULD catch it. The
stage pin catches «refusal became a wrong answer». It does not catch
«refusal became a crash or another refusal».

**(b) A crash at the same stage as a named refusal.**
`arrays/materialization-budget/over-budget` (BUG-078) is a by-name budget
refusal at `lean-observation`. Before BUG-078 this exact shape was a native
stack overflow. If the `arrayLenBudget` arm regressed, the run would die on
SIGSEGV or SIGABRT. The runner reports `Lean run KILLED (exit 139 …)` at
`lean-observation`, and the baseline matches. This is not hypothetical.
`strings/trimspace-repeat/repeat-bound-refused` (BUG-090) sat at
`FAIL/lean-observation` as `Lean run KILLED (exit 134 … Stack overflow)`
while BUGS.md called it a named bound. The gate was green, and the
release-readiness review found it (item 9, fixed in train 2). The same
holds at `frontend-export`: a frontend OOM-kill (137) or panic (exit 2)
matches any of the 34 export-time refusals there. At `confluent` and
`membership`, an enumerator `KILLED` matches the enumerator's named refusal
(`goroutines/worker-pool/sum`).

**(b′) A wrong answer at the same stage as a designed red** (a sub-case,
`lean-observation` only). `floats/to-int-out-of-range/nan` is pinned
`FAIL/lean-observation` as the R6 latitude refusal (`unsupported`). If the
refusal arm were replaced by a machine `panic`, the runner would write
`expected status ok, got {…"status":"panic"…}`, a wrong answer at a forced
point. That is the same stage, so it matches. This applies to the 33
`lean-observation` FAIL rows: the status inside the detail is not pinned.
It cannot happen on the 191 `frontend-export` rows, which produce no
observation that could be wrong.

**(c) A negative row never consults GoLean.**
`imports/package-mismatch` passes because gc says `found packages`. GoLean
refuses it today only through `fileselect.go`, the BUG-108 boundary, and
not through type-checking. Suppose a frontend change relaxed file
selection, or a load-path change stopped surfacing go/types errors for some
package (for example, the frontend type-checked only the files it lowers).
The frontend would then lower an illegal program, and the machine would run
it. All 394 negative rows would stay PASS, because no row runs the
frontend. The same holds for every `goto`-over-declaration or
label-misuse row (`control-flow/goto-over-declaration`): GoLean's own goto
hoisting (FR-11/FR-20) sits right next to these rejections.

**(d) A red-by-design row whose refusal no longer names its bug.**
`check-bugs` (check 1, `scripts/check-bugs.sh` around line 114) verifies an
`Expect: FAIL` entry's cases against the BASELINE: `open/FAIL/*` passes, so
neither the stage nor the text is checked. It has no access to the detail
at all, because the baseline does not store one. Take BUG-124's six
`interfaces/uintptr-identity/*` rows, the by-name refusal landed in train 3.
If the uintptr refusal were dropped and the rows instead hit FR-7
`tuple-iface-box` (same stage), or the frontend crashed, all six would stay
`FAIL/frontend-export`. `Expect: FAIL` would hold and the baseline would
match. The same goes for BUG-093's eleven `builtins/print/refused/*` rows
and BUG-094's seven NaN-payload rows. This covers 33 rows on 6 entries.

## 3. Options

Gate cost is per gate run. «Measured» means this lane timed it on main's
data.

| | what changes | catches | sessions | gate cost | migration (re-pin) |
|---|---|---|---|---|---|
| **A** cause column | `baselines/native-full.tsv` gains column 4 `cause` (`-` on PASS rows); new `scripts/coverage-cause` derives the key from a results row's detail; new small machine-refusal table (~15 rows); `coverage-baseline-diff` compares `result/stage/cause`, with the alternation rule extended to the cause column; one line in `diff-coverage` to record the frontend exit code in the detail | a, b, b′, d on all 239 FAIL rows | 1 (+0.5 with the negative leg) | < 3 s: lowerdiag classify over the 191 frontend texts **16 ms measured**; one `go build` of lowerdiag (the package objects are warm after ci's `go test ./tools/lowerdiag`; the frontend's cold build measured 4.3 s here); awk for the rest | one re-pin: 3953 rows gain a column, 239 non-`-` keys, 0 result/stage moves |
| **B** refusal lane | manifest grammar: `lane=refusal` + `expect_cause=`; runner asserts the text; baseline unchanged | a, b, b′, d, but only for rows migrated into the lane | 2 | ~0 | 239 manifest rows re-laned (cases.tsv edits across many dirs). Their result changes: **a matched refusal would read PASS**, which contradicts the doctrine «an `unsupported`/`stuck` outcome never counts as a pass» unless it gets a new result word (a larger change than A) |
| **C** crash stage + BUGS text | `diff-coverage` reports non-verdicts at a new stage `crash` (frontend exit 2/signal/timeout, Lean signal/timeout, enumerator signal); `crash` joins `STAGE_VOCAB` and check-bugs' fidelity set; `Expect: FAIL` entries gain `- Cause: <key>`; check-bugs reads `latest.tsv` to assert it | b everywhere; a, b′, d on the 33 `Expect: FAIL` rows only | 1 | < 1 s | 0 rows today (0 non-verdicts measured); 6 BUGS entries gain a line |
| **D** crash stage only | C's stage split, nothing else | b only (not a, b′, d) | 0.5 | ~0 | 0 rows today |

**Option A's key grammar** (one value per row, fail closed). The first rule
that applies wins:

1. Runner non-verdict phrases, at any stage: `KILLED (exit N` →
   `killed:N`; `TIMED OUT after` → `timeout`; `failed with exit N (did not
   decide)` → `undecided:N`. The phrases come only from `signal_cause` and
   `undecided_cause` (`diff-coverage:167-197`), a fixed vocabulary.
2. `frontend-export`: frontend exit 2 → `crash:frontend` (needs the one-line
   runner change; Go exits 2 on panic and fatal, and the frontend's only
   deliberate exit is 1, `tools/nativefrontend/main.go:29`). Otherwise
   extract the JSON `message` if it is a run-time stub, then
   `lowerdiag classify` → the cause **id** (`FR-15/complex`). Unclassified →
   `fe?:<lowerdiag's 8-word head>`, which is pinned and also reported as a
   speedbump.
3. `lean-observation`: `<status>:<machine-table id>`, with the status read
   from the observation JSON, or from the variant-stream phrase `the machine
   produced status '<s>'` (`unsupported:float-to-int-range`,
   `stuck:nil-slice-base`, `race:race`, …). An unmatched message →
   `<status>:?`. A non-JSON capture → `crash:lean-output`.
4. Every other stage (`differential`, the oracle-side `go-*`, manifest) →
   `-`. Their stage already names the verdict. Pinning the wrong VALUE of
   the 4 differential reds is possible (`diff:<sha8 of Lean obs>`), but they
   are known records; see D4.

The stage alternation on `channels/select-select/beside-loop` becomes a
cause alternation under the same `# reason:` block
(`unsupported:select-select|-`).

**The churn cost of A, honestly.** A row that is red today and moves from
one refusal to another stays FAIL, so today it is silent. Under A it becomes
drift and needs a re-pin line. The usual case is a feature lane landing FR-n
while the program then hits FR-m. That is the signal F9 asks for, and the
lane that caused it records it. The raw text is no key: it carries run
paths (the BUG-078 row's detail names the `train3-1012` worktree). Pinning the cause **id** rather than the
templated key or the raw text limits churn to real cause moves. Rewording a
frontend message moves nothing unless it breaks a `causes.tsv` regex. If it
does, the row shows `fe?:…`, which flags a stale classifier (the
`TestVocabularyCoverageIsTracked` concern) and is worth fixing anyway.

**The negative corpus: what GoLean-side assertion, and where.** The
assertion belongs to the FRONTEND, not the machine. A gc-rejected program
never yields a wire, because go/types or go/parser rejects it first
(measured 393/394; the 394th is the file-selection boundary). «Frontend
lowers, machine refuses by name» is therefore not the contract. If it ever
happened, that would be the defect. Proposed per-row leg in
`coverage-negative`: after the gc check passes, run the frontend.

- PASS iff it exits 1 with class ∈ {`type-check`, `parse`, `file-selection`}.
- `FAIL/frontend-accepts`: exit 0. GoLean lowers a program gc rejects, a
  trust-surface #1 defect.
- `FAIL/frontend-crash`: exit ≥ 2.
- `FAIL/frontend-reason`: exit 1 with another class, e.g. `unsupported:
  complex` on a program with a type error. The type checker missed it, and
  the row would start lowering once FR-15 lands.

The class goes in the detail. The baseline format is unchanged, and all 394
rows stay PASS (measured), so this needs no re-pin, only a header line. The
cost is 41.8 s serial in the `--diff` tier only (the fast tier judges the
recorded run), about 4-5% of an 850-1034 s `--diff`. Running the frontend
with `xargs -P` would cut it to a few seconds, but the loop is simple, and
parallelism should wait until the 42 s is shown to matter. F9's other half,
malformed-wire decoder tests, is a different surface (`NativeToIR.lean`
unit tests) and is out of this lane (D6).

## 4. Recommendation ([AGENT])

**Option A plus the negative frontend leg.**

The charter question is whether the current gap lets a wrong answer or a
crash pass for a designed red at the gate. Yes for a crash: §2b's
`repeat-bound-refused` did exactly that until item 9, and the mechanism
still covers all 239 FAIL rows, because the 0 non-verdicts today are
luck and not a property. Yes for a wrong answer, but narrowly: the 33
`lean-observation` FAIL rows (§2b′), whose status inside the detail is
unpinned. No for the 3714 PASS rows: the gate's central claim, observed ∈
modeled, is untouched. No for wrong answers on the 191 `frontend-export`
rows, which produce no observation. The negative lane's
gap is a missing check on trust surface #1 (the frontend), not a weak one.

Why A over C or D: the baseline diff is already a GATE on trust surface #2,
so pinning one more column inside it adds no gate (the cull rule). It costs
under 3 s, and it covers all 239 rows with one mechanism. C reaches the same
end through the BUGS.md ledger for 33 rows only, needs a second data path
(check-bugs reading `latest.tsv`), and leaves the 162 unledgered frontier
reds pinned by stage alone. D is the floor if A is declined: it closes (b),
the class that actually happened. B conflicts with the doctrine (a refusal
must never read PASS) and costs the most.

**Lane plan** (`fix/refusal-cause-pin-<date>`, worktree, one session plus a
half):

1. `scripts/diff-coverage:863` (and the membership twin `:1719`): record the
   frontend exit code in the detail (`native frontend (exit N): …`). The
   frontend and membership arms only; no stage moves.
2. `scripts/coverage-cause` (new, about 100 lines of bash/awk plus one
   batched `lowerdiag classify` call): read a results TSV and print `id ⇥
   cause` per §3's grammar. Extract the JSON `message` before classifying
   (this clears the 3 UNCLASSIFIED rows). Exit 2 on unreadable input.
3. `scripts/machine-causes.tsv` (new, about 15 rows, `id ⇥ status ⇥
   substring`), seeded from §1.2's 15 messages. A comment header says what
   it is and that unmatched rows key as `<status>:?`.
4. `scripts/coverage-baseline-diff`: read baseline column 4 (absent ⇒
   REFUSED, exit 2: the format is required, never defaulted). Compare it
   against `coverage-cause` on the results. Extend the alternation
   validation to the cause column. Print `baseline[R/S/C] -> now[R/S/C]`.
   The negative baseline keeps 3 columns (the tool takes `--no-cause` for
   it; explicit, never inferred).
5. Re-pin `baselines/native-full.tsv`: regenerate data rows with the cause
   column from the recorded run at the lane's base. **Re-pin reason**:
   «cause column introduced (release-readiness item 8 / gate-audit F9,
   [USER]-approved D1); 0 result/stage moves; 239 FAIL rows keyed; the key
   grammar is this note §3». The forward re-pin guard is unaffected (it
   reads columns 1-2). Confirm that `check-bugs`, `check-coverage`,
   `oracle-version-sweep` (retired 2026-10-13, superseded by `scripts/go-version-diversity`: it floated the frontend with the oracle and judged result/stage only), `choice-trace-summarize` and the lowerdiag test
   read only columns ≤ 3 (checked here: all index columns 1-3 by position).
6. `scripts/coverage-negative`: the frontend leg of §3, using the frontend
   built at `artifacts/coverage/bin/nativefrontend`, or built by the
   script, refusing by name if it is absent. Add the new stage words to the
   vocabulary. Add a negative-baseline header line, with no row change.
7. Docs: `docs/coverage-suite-structure.md` (the baseline paragraph at
   :166, «result/id/stage only»), `docs/cli.md` if it documents the
   baseline, and `CLAUDE.md`'s gate list unchanged in wording (still «the
   baseline diff»). Item 8 is marked landed.
8. Gate: `capped scripts/ci` (fast tier) at each commit. `capped scripts/ci
   --diff` before the merge ask. Test by hand: one FAIL row's detail edited
   to `Lean run KILLED (exit 139 …)` in a scratch copy of the results must
   drift. That is a hand-run check, not a gate.

## 5. Decisions for the [USER]

1. **D1, the baseline-format change**: add a `cause` column to
   `baselines/native-full.tsv`, compared by the gate (Option A).
   *Recommend: approve.* If declined, *recommend D* (the crash-stage split,
   0 re-pin rows today).
2. **D2, key granularity**: pin the `causes.tsv` cause **id**
   (`FR-14/stdlib-package-unmodeled`), the templated key (`os.Getenv`; 59
   values vs. 36 ids today), or a raw substring. *Recommend: the id.* It is
   stable across rewording and fixture renames, and a cause move is the
   signal.
3. **D3, the negative frontend leg as a GATE** in `coverage-negative`. A
   row passes iff gc rejects with the substring AND the frontend exits 1
   with class type-check / parse / file-selection. No negative re-pin (394
   measured green). Adds 42 s to `--diff`. *Recommend: approve as a gate*,
   because it is the only check that the trusted frontend does not lower
   programs gc rejects.
4. **D4, scope of pinned stages**: `frontend-export`, `lean-observation`,
   and runner non-verdicts at every stage; `-` for `differential` and the
   oracle-side `go-*` stages. *Recommend: as stated.* Pinning the wrong
   VALUE of the 4 differential reds is cheap but adds churn for known
   records, so leave it out.
5. **D5, unclassified texts**: pin them as `fe?:<head>` / `<status>:?` and
   report them under the speedbump heading (recommended), or fail the gate
   on any unclassified FAIL row. *Recommend: pin + speedbump.* Failing the
   gate would make `causes.tsv` completeness a gate on a non-trust table
   (gate cruft).
6. **D6, scope**: F9's malformed-wire decoder tests (missing types, bad
   indices, duplicate ids) are a separate item, not part of this lane.
   `check-bugs` stays unchanged (no `- Cause:` line; A covers it).
   *Recommend: agree.*
