# Review: the defect record's completeness and shape classification

Reviewed: branch `records/defect-shapes-1027` at `d0c7631c` (three commits over
main `aa49ebcf`): the 23 late entries BUG-137–159 in `docs/BUGS.md`, the
classification `docs/defect-shapes.md` (25 shapes, 159 rows, the step-2 order
and axes), and check (7) in `scripts/check-bugs.sh`. Reviewer: [AGENT],
independent of the lane, 2026-10-27, in worktree
`.claude/worktrees/review-shapes-1027`. The question put: is the record
COMPLETE, and is the classification FIT for a sweep that spends one lane per
shape.

Method. Read the charter, the campaign plan (§2–§5), the index header and all
23 late entries. Ran `scripts/check-bugs.sh` on the branch. Re-derived the
counts of `defect-shapes.md` from its own rows. Checked every cited commit of
the late entries against `git log` on main, and the pre-fix and post-fix
baseline rows for a sample. Swept the history independently: 2,671 commits
on main since 2026-07-01, of which 789 match wrong-answer terms (mismatch,
oracle, diverge, fidelity, stuck, panic text, off-by, regression, wrong,
twice, eager, false/missed race, wedge, fuel-out, red-first, …) and cite no
hash the index cites; each of those was read by month (five sub-sweeps), with
the non-matching commits skimmed by subject, the review documents, the
2026-08-19 triage table, the arc logs, the latitude inventory, the changelog
rows, the deep-clean pass and the train-20 stage and audit branches
cross-checked against the index. Every candidate below was then verified by
me from the commit and the baselines; the sub-sweeps' rejected lists are
summarised in §3.

## 1. Findings

Severity: HIGH = the sweep would search a wrong or missing neighbourhood;
MEDIUM = a wrong claim in the record or an inconsistency the owner should
settle before step 2; LOW = a defect in the document that does not misdirect
a lane.

### F1 — HIGH — the 2026-08-19 "19-red" families L1, L2a and L3 have no entry; BUG-151 (L7) was entered from the same table

What. `docs/2026-08-19_triage-table.md` §3.3 lists category (a) rows L1, L2a,
L3, L7, L10, all "wrongly stuck/refused at the machine on a supported
construct". The lane entered L7 (BUG-151, citing "§3.3, L7, category (a)")
and none of the others:

- L1, commit `67242a4c`: `[]rune(s)` / `string([]rune)` lowered by the
  frontend and refused by the machine's conversion catch-all (`Ops.lean`,
  `unsupported "conversion to …"`), gc green. Nine rows
  (`strings/rune-slice-conversion`, `strings/rune-string-conversion`,
  `strings/string-to-rune-copy`, `strings/rune-slice-to-string-copy`,
  `strings/rune-invalid-values`, `strings/defined-slice-string-conversion`,
  `strings/nil-slice-string-conversion`,
  `spec-examples-decl/string-from-runes`,
  `spec-examples-lexical/string-to-runes`).
- L2a, commit `0a786453`: slice→array / array-pointer conversion with
  `len < N` refused at the same catch-all where gc raises the recoverable
  `cannot convert slice with length …` panic. Rows
  `spec-examples-decl/slice-to-array/{short-array,short-array-ptr,nil-to-longer-ptr}`.
- L3, commit `e4b8c87c`: `min`/`max` over float operands refused
  (`Machine.lean` `minOf`/`maxOf`, `unsupported "min builtin over float
  operands"`) where gc computes the IEEE result. Rows
  `spec-examples-stmt/min-max-float-specials/{infinities,nan,signed-zero}`.
- L10, commit `fe713c0b`: `go` of a nil func value refused where gc raises
  `fatal error: go of nil func value`; row `goroutines/spawn-edge/nil-func-fatal`.
  Arguable: the refusal was a named placeholder pending the `fatal` class.

How verified. `git show 67242a4c^:baselines/native-full.tsv` has
`strings/rune-slice-conversion` and `spec-examples-lexical/string-to-runes` at
`FAIL lean-observation`; at `67242a4c` both are PASS. The L2a and L3 rows are
PASS in today's baseline. None of the row names or hashes appears in
`docs/BUGS.md` (grep: 0). BUG-020's text still says string→[]rune "remain
refused" and "stay untriaged" (lines 7 and 35 of the entry) — the same
stale-sentence situation BUG-151 corrected for L7.

Why it matters. These are the index's own precedent class (BUG-020 and
BUG-103 are the same catch-all's missing arms; BUG-077 the `.nilLit`
sibling). L1 and L2a are S2 members and
S2 is Tier-1 position 2: its lane would start with an instance list missing
two members and the `[]rune` / slice→array cells. L3 is an S11 member.

### F2 — HIGH — the semantic core's absorbing-default shape has no home; S24 is cut as "tool boundaries" with axes that exclude the core

What. The plan's §3 seed vocabulary names "an absorbing default (`| _ => false
/ none / the input`) reads a malformed or unexpected shape as benign", and §1
cites DC11 (the pool's `wakeReady` reading a load failure as "not ready",
`Multi.lean`) with its sibling in the enumeration mirror (train-19 shake F3)
as the motivating instance. In `defect-shapes.md` the only shape with
"fail-open defaults" in its name is S24, defined as "at the decoder, the CLI
or an apparatus script", with axes `NativeToIR.lean` `| _ =>`/`getD` arms,
`CLI.lean`/`ChoiceTrace.lean` IO, `scripts/*`. The core's arms are nowhere:
BUG-085 (`Ops.lean` `storeLoc` materializing a phantom cell — a core arm) is
filed in S24 whose axes do not list `Ops.lean`; BUG-039 (a fail-open
predicate) in S8; BUG-154 (a refusal absorbed by `recover`) in S21; DC11 has
no entry (recorded inside BUG-133 as "not a fidelity bug", a defensible
ruling) and so no row in §2 at all.

How verified. Read the S24 legend row and §3 item 4; grep of `| _ =>` in
`GoLean/GoCore/`: `Ops.lean` 28, `Machine.lean` 69, `Multi.lean` 31,
`StepErrors.lean` 13, `Consumes.lean` 16 (an upper bound on the arms a lane
would read; most are legitimate). `docs/BUGS.md` cites DC11 twice, inside
BUG-133 only.

Why it matters. A sweep lane follows the axes line. As written, no lane will
enumerate the core's absorbing arms — the one seed shape whose instances
(DC11 → F3, BUG-085) were found by reading, not by the differential, and
which the §4 method (probe gc vs model) cannot find. Either give it a shape
(enumeration by reading: every `| _ =>` arm of `Ops`/`Machine`/`Multi`/
`StepFn` whose default is a value rather than a named error, with DC11/F3,
BUG-085, BUG-039 as members and "reachable from admitted source?" as the
verdict column) or write its exclusion and the reason into §3 "Not
scheduled". Related: F5.

### F3 — MEDIUM — two defects fixed by `923e3ec0` (2026-07-26) have no entry

What. The commit "Builtins: delete/clear/min/max + string conversions + decl
quarantine" records (a) `[]byte(s)` / `string(b)` / `string(r)` "were latent
backlog reds emitting the unsupported generic convert" — the frontend routed
the three conversions to the generic `convert`, which the machine refused;
and (b) "emitAssign's speculative emitCallNode ran hoisting builtin emitters
TWICE (copy executed twice …)" — `x := len(f())`, `make([]T, f())` evaluated
`f` twice, a wrong value with status ok.

How verified. (a) `strings/byte-slice-to-string-copy`,
`strings/string-byte-conversion`, `strings/string-int-rune` are
`FAIL lean-observation` at `4dc23653` (main, the slice-0 re-pin) and PASS at
`2b495d28`; none of the three ids is in the index. (b) The commit's own
words; the fix's rows (`builtins/copy-edge/*`) were `frontend-export` on main
because `copy` lowered on the same branch, so reachability on main rests on
the code at `923e3ec0^` (the speculative path called `emitBuiltin`, whose
`len`/`cap`/`make` arms hoist and return `effectful=false`, so the RHS was
re-emitted) — the same kind of argument BUG-140 makes for its slice-index
form. BUG-047 cites the `isBuiltinCall` guard as context and `x := len(bump())`
as a control, never as a fixed defect.

Why it matters. (a) is the BUG-020/BUG-141 class (a supported construct
refused at the machine, not the boundary) and an S2 instance; (b) is an S9
instance (the lane's own BUG-140 precedent).

### F4 — MEDIUM — `31eeb6dd` (2026-08-05) is unrecorded and BUG-149's new text states the opposite of it

What. BUG-149 (late entry) says "the deferred-call frame entry deliberately
kept the thrown behaviour (a panic during unwinding, a recorded narrowing at
the time)". The same day, commit `31eeb6dd` "Audit F1+F5: deferred-call
frame-entry panics are recoverable (all three drain sites, lockstep)" retired
that narrowing: a dispatch panic entering a DEFERRED call "escaped as an
unrecoverable error: status 'panic' on programs Go completes"; three rows
`defer/deferred-dispatch-entry-panic/{return-drain,fallthrough-drain,during-panic}`.

How verified. The commit message; the three rows PASS in today's baseline;
`grep deferred-dispatch-entry-panic\|31eeb6dd docs/BUGS.md` → 0.

Why it matters. A wrong statement inside a brand-new entry, and the three
drain sites are S12 cells (the recover walk) the lane would otherwise believe
are still narrowed. Caveat the sub-sweep raised: the route (`defer i.M()` on
an interface) was refused by the frontend before the same arc, so under the
lane's "same-branch" rule this may be a sentence in BUG-149 rather than an
entry; either way the entry's sentence must go.

### F5 — MEDIUM — S24 sits at Tier-1 position 4 with apparatus members, and the apparatus rule is applied inconsistently

What. The plan's order puts "absorbing defaults" third among wrong answers
with status ok. The lane filled that slot with S24, whose members are
BUG-110/119/120/122 (CLI and decoder robustness), BUG-117 (a script's
record), BUG-091 (export nondeterminism) and BUG-085 — none a wrong answer on
a Go program. Meanwhile the deep-clean pass fixed six apparatus fail-opens of
exactly that mechanism on main (DC02 `348a7a78`, DC03 `bea043c6`, DC08/09/10/18
`d4bc0442`) and none has an entry, while DC06 (BUG-158) was entered "for
consistency". The index's header defines fidelity bugs only; its practice
since BUG-110 includes apparatus fail-opens. The lane's completeness rule
("fidelity fixes") is narrower than the index's practice, so the record is
complete for one reading and inconsistent for the other.

How verified. The S24 row and §3 item 4; `git log --since=2026-10-25` for the
DC commits; `grep DC0 docs/BUGS.md` → DC01, DC06, DC11 only.

Why it matters. Position 4 spends an early lane on robustness, not fidelity,
and that lane's instance list is missing its most recent instances (the plan:
most recent first). Remedy: decide whether apparatus fail-opens are in the
index (then enter DC02/03/08/09/10/18 and, when fixed, DC07 — open, assigned
to no lane); and move S24 to a tier of its own (its "probe" is a mutant set
and a review, not gc), so that the plan's slot 3 is the core shape of F2.

### F6 — MEDIUM — BUG-138 is filed under S17; its mechanism is byte transparency of a string-carrying channel, shared with BUG-105 (S22)

What. BUG-138: the wire carried string literals as JSON strings and
`encoding/json` replaced invalid UTF-8 with U+FFFD — a lossy encoding, silent.
BUG-105: NUL/SOH in panic payloads lost at the observation transport — the
same mechanism at the readout. The lane put "byte escapes" into S17's
definition (statement forms, spellings, synthetic symbols) and BUG-105 into
S22. DC07 (the observation comparator accepts lossy JSON and impossible byte
values) is open, unfixed and in neither.

Why it matters. S17's axes (each `*ast.Stmt`/`*ast.Expr` arm × spellings)
will never enumerate byte transparency. The neighbourhood is: every
string-carrying channel (wire literals and constants, rune/byte literals,
panic payloads, `print` output, the observation JSON, refusal texts, seed
input, struct tags) × byte classes (invalid UTF-8, NUL, surrogates, control
characters, the SOH family). One shape, or one named axis under S24/S22,
with BUG-138, BUG-105 and DC07 as members.

### F7 — MEDIUM — the entry rule for envelope-too-narrow at a latitude point is applied inconsistently (BUG-159 in; R15 and E7 out)

What. BUG-159 (late, open) enters the abort window: gc's dominant member
outside the modeled set, ruled a stated limit. `pointers/zero-size-address/
escaped-same` (latitude inventory R15: machine 0 vs gc 1, "observed ∉
modeled-singleton at a latitude point", a live `FAIL differential`, a
re-envelope obligation on the backlog) and `init/hidden-dep-order` (E7, a
live `FAIL differential`) have no entry; the lane's §4 states the E7 decision
and does not mention R15. BUG-021, BUG-118, BUG-123, BUG-152 are entries of
the same class (envelope too narrow at an implementation-specific point).

How verified. `scripts/check-bugs.sh --list`: 14 unexplained fidelity
failures, the two rows among the four dispositioned `latitude` in
`baselines/untriaged-ids`; the inventory's R15 and E7 text; the equality
review's F5 calls R15 "a latitude" (consistent with the project's standing
position, which is why this is MEDIUM and not HIGH).

Why it matters. Either rule is defensible; applying both leaves the S4 lane
(zero-size values are on its axes) and the S19 lane without the instance on a
Cases line, where check (1) would hold it. Settle the rule in §4 and apply it
to BUG-159, R15 and E7 alike.

### F8 — MEDIUM — the "pre-index" exclusion is the lane's own rule, not the plan's, and it hides three defects on main

What. The lane's commit says the 2026-07-18 panic-prefix fix `18df1672`
"predates the index and is not entered". The plan (STATUS paragraph and §2)
has no date floor: the history is to be read for every semantic defect. The
same rule hides `b0b75abe` (2026-07-18: `decodeFor` lowered the three-clause
`for` so that `continue` skipped the post statement — an infinite loop where
gc completes; and blank call-result discard temps always typed `int`,
corrupting non-int discards; rows `control-flow/for-continue-post-plain`,
`multi-assign/blank-discard-nonint`) and `b2d240d7` (2026-07-18: an integer
literal at a defined integer type carried the default `int` kind;
`emitConstValue`). The index was born 2026-07-19 (`a359e97a`); the native
frontend was on main from 07-17.

How verified. The commit messages; the rows exist and PASS; neither hash nor
row is in the index (`blank-discard-nonint` appears once, as a control in
BUG-035).

Why it matters. Four or five entries, each a shape instance (S9/S13-adjacent
for `continue`/post; S11 for the kinds; S12 for the texts). The owner may
rule them out; the rule should be a recorded decision with the candidates
named, not an unstated floor.

### F9 — LOW — the train-20 scope: one over-acceptance fix and two open findings of the same class, unentered

What. The lane's scope includes the stage (BUG-134–136). On that stage,
`6ce62599` also fixed the shake review's F2 (`go 1.26.5` + `toolchain
go1.26.5` accepted and RUN where gc refuses; negative row
`modules/toolchain-redundant`) — the BUG-158 class the lane entered "for
consistency", with no sentence anywhere. On the unmerged audit branch
`audit/train20-apparatus-1026` (`53df8e0d`), F1 demonstrates a wrong value
with status ok (an env-file `GOWORK`, or `GOFLAGS=-modfile` carrying `godebug
panicnil=1`: gc `true`, machine `ok`/`false`, cases w13/w27/w28) and notes
that BUG-135's text says the gap is over-refusing only; F4 lists six go.mod
shapes gc rejects that the scanner exports, pre-existing on main. Both are
pending disposition; neither has an entry.

Why it matters. S20 is Tier-1 position 5; its lane should take these as
instances, and the index needs the open entry when the audit lands.

### F10 — LOW — the §3 claim that member lists are most-recent-first is false for 14 shapes

What. §3 says "the member lists below are in that order" (most recent
instance first). The lists are by id descending, so the July late entries
lead: S12 has 137 (fixed 07-25) before 087 (09-03) and 059; S5 has 143
(07-25) before 095 (09-05); likewise S2 (151 before 103), S7, S9, S13, S8,
S15, S16, S17, S20, S21, S3, S6.

How verified. A script over the entries' fix dates against the lists.

### F11 — LOW — S17 bundles three mechanisms; its axes cover two

What. Members: missing emitter arms (001, 012, 024, 141, 147), spelling
admission (115, 136), synthetic-symbol bookkeeping (027: `$deferClose<N>`
qualification; 031: the `deferNoopEmitted` rollback with the quarantine),
plus 138 (F6) and 057 (a wrong value with status ok in a Tier-2 shape). The
axes line names the arms and spellings; the synthetic symbols need their own
axis (every synthetic symbol × scope it is keyed by × every rollback path).
S12 similarly bundles payload construction, text rendering and the recover
walk; its axes do name all three, so a lane can proceed.

### F12 — LOW — check (7): two silent exemptions and a hygiene hazard

What. (a) An entry whose Status line carries no date is exempt; a new fixed
entry written without a date passes silently — a fail-open in a report-only
check. Twenty of the 156 Status lines carry no date today, all old; the
exemption could instead apply only to entries below BUG-137, or the check
could report "undated" by name. (b) A re-fix after the campaign recorded by
amending an old entry (first date earlier) is exempt by construction;
acceptable, but say so in the header. (c) The literal NUL byte in BUG-105's
text (`docs/BUGS.md:7228`) is read correctly by gawk (all 156 ids seen; the
existing parser has the same exposure), but POSIX leaves NUL in awk input
undefined and `grep` needs `-a`/`-P` to see it; replace it with an escape in
the prose. Found sound: the awk's date rule and first-date match; the
`fixed,`/`fixed:` spellings are already a check (0) FAIL in the main parser,
so they cannot slip past (7); the fixture test behaves as the commit says
(an undated 2026-10-27 entry named, the dated-2026-10-26 one not); on the
real index nothing is reported and the 23 lines are present.

### F13 — LOW — stale sentences the lane saw and left

BUG-020 still says `structs/tag-pointer-conversion` is "now stuck at field
access" (BUG-151 quotes the sentence as stale) and that string→[]rune
"remain refused" (F1). A records-only lane could have corrected both in
place.

### F14 — LOW — the rejected candidates are not recorded for the step-2 lanes

The lane's commit names its rules but not the candidates it rejected under
them. The same-branch rule is right for the index (a defect never on main is
not the product's) but those defects are shape evidence for the sweep — e.g.
`084b1f4f` (2026-08-06, same-branch: waiter-queue priority and
waiter-extended select readiness, "both UNREACHABLE outcomes in the current
model", an S15 shape), `c6886a99` (same-branch: `%x`/`%q` over a Stringer
rendered silently wrong, an S21 shape). A short list in §4 (hash, shape, why
excluded) would let the S15/S21 lanes start from them.

## 2. Checked and found sound

- `scripts/check-bugs.sh` on the branch: ok, 156 entries; every late entry's
  differential Cases row exists and PASSes (check (3)); BUG-153's three
  `Expect: FAIL` rows FAIL (check (5)); the unexplained set is unchanged
  (14: coverage 10, latitude 4, wrong-answer 0). The negative rows BUG-157
  and BUG-158 cite exist and PASS in `baselines/negative-full.tsv`.
- All 23 cited commits exist on main; the messages of `1ca39648`, `f64bfc89`,
  `cc3ed039`, `75e03555`, `c908921e`, `e2df3535`, `1ac3261a`, `1e080a83`,
  `7ce738bc`, `633a3307`, `70f9c94a`, `00c2bd56`, `a4ce5c5e`, `86d30a23`,
  `b99d016b`, `fe730d81`, `3ee028ec`, `91c6333f`, `ae44faee`, `211f8b0f`,
  `42893297`, `71bb9cd4`, `348a7a78` say what the entries say; `7ce738bc`
  and `1e080a83` themselves state the "pre-existing" claims BUG-144/145/143
  rest on. Pre-fix FAIL verified in the baseline at the fixing commit's
  parent for BUG-139 (`variadic/forwarding`, `no-args-vs-empty-spread`:
  FAIL differential), BUG-140 (`structs/selector-eval-once`), BUG-147
  (`variadic/variadic-method`), BUG-151 (`structs/tag-pointer-conversion`).
- Each of the 23 is a fidelity defect by the header's definition, with the
  qualifications the entries themselves state: BUG-157/158 are
  over-acceptance (said so, with the owner's option to strike), BUG-155 a
  wrong program with a clean export, BUG-150 a defect against the language
  the model claims rather than against the oracle of the day (said so),
  BUG-159 an open stated limit (a proper open entry). BUG-140's claim that
  BUG-001 records it only as a sentence is true (BUG-001's fix paragraph).
- The lane's same-site-and-shape rule was applied consistently where
  tested: BUG-115, BUG-048, BUG-058, BUG-003 do not record the July/August
  fixes that BUG-141, BUG-143, BUG-144, BUG-148 now enter; BUG-148's
  cond-capture row is correctly excluded as same-branch; the E7 decision is
  written down.
- Counts: the legend's member counts sum to 159 and equal the row counts per
  shape; the §3 member lists equal the rows (S25 under "Not scheduled"); 142
  fixed / 17 open / 12 red-by-design / 3 stage reconcile with the plan's
  133 (117 fixed, 16 open, 11 red-by-design) + 23 late (22 fixed, 1 open, 1
  red-by-design) + 3 stage; swept 3 / partial 63 / unswept 92 + BUG-002.
- Placement, random five (seeded): BUG-013 → S22, BUG-052 → S8, BUG-053 → S5,
  BUG-055 → S11, BUG-056 → S10 — where I would put them. Deliberately hard:
  BUG-111 → S4 (the `Loc` representation as identity, the detector a
  consumer), BUG-088 → S14, BUG-130 → S9, BUG-099 → S12, BUG-017/079 → S1,
  BUG-039 → S8, BUG-146 with BUG-052 → S8 — defensible, the §4 resolutions
  say why. BUG-139 → S4 is a stretch (the mechanism is a value-producing
  site minting empty where Go has nil, not a comparison) but S4's axes name
  the packing sites, so a lane finds it.
- Cut by mechanism with axes a lane can start from: S6 (the two-phase
  spine, 11 members, one site family), S8 (the unseq axis), S1/S2 (every
  assignable context / every `convertValueToTy` target), S3 (every `Ty`
  key), S5, S7, S9, S13, S15 (`Config.atBoundary`'s arms), S16 (every
  op's footprint × key kind), S18, S19, S20 (what the go command reads ×
  gc's whole-program rules), S21, S23. The Tier-1 order follows the plan's
  named sequence (identity, conversions, [slot 3], admission, panics) apart
  from F5.
- The history sweep found no omission in September (the one borderline,
  the six `-race` verdicts of the C1 S2c audit, is on BUG-111's Cases line)
  and none in October beyond F9; the lane's reading of the audit-response
  commits that produced BUG-148/149/150 was good, and its rows for the
  triage table's L5/L6 (BUG-038 records them) and A3/A6/A7 are covered.
- Merge mechanics: BUG-137–159 are appended after BUG-133 on this branch
  while BUG-134–136 are appended at the same place on the stage; the
  ff-only protocol will need a trivial rebase of one onto the other, and
  BUG-151's and §2's references to BUG-134 dangle until the train lands.

## 3. The sweep's rejected candidates, summarised

Per window, after reading: July 98 candidates and ~240 others — rejected as
coverage (frontend-export → PASS flips, e.g. `9aa3fb4f`/`10a6c08c` 26 flips,
`175a8062`), latitude (`b7dd0fac`, map-range picks), apparatus/proof-layer
(the Arc B–E and gate commits), same-branch (`bc296bef`, `9024aeb8`,
`175a8062`'s recover discard, `e2df3535`'s lifted-literal collision,
`f64bfc89` findings 2–3, `c22bc182`'s twelve other findings on the
quorum-pilot branch), already recorded (`85f36598` → BUG-006/004/007,
`bfe5496f` → BUG-009/010/005, `c908921e`'s 36 flips → BUG-001/140/141).
August 1–15: 251 candidates — same-branch under the arcs' pre-merge audit
cycle (`084b1f4f`, `75ce6c13`, `da84c1ac`, `c7ac2c9a`, `d29a16ef`,
`be2f46ae`, `f21dcd2a`, `f1965d7e`, `357ed8da`, `c883267a`, `9757f45d`),
coverage (`1c777769`'s eight flips all frontend-export, `0c04d548`,
`bbf81870`, the quarantine lifts), latitude (`0beaa896` → BUG-118), already
recorded (`a38e086e` inside BUG-020, `12f2d42c` inside BUG-025/022). August
16–31: 188 candidates and 51 runtime-touching commits — the W4.x audit
rounds are same-branch (`c6886a99`, `0bb74f18`, `56a12142`, `279164e0`),
coverage (`f495724e`, `3e99c403`, `7d88db76`), latitude (`cfac86bb` R15),
recorded (`ee5f744a` → BUG-060/061, `8aa97076` → BUG-068, `c6c4cffe` →
BUG-066/067). September: 134 candidates and 167 runtime-touching commits —
same-branch fix rounds (`f5f84595`, `7a5cd534` R1, `42893297` R1'-1/2/4,
`8ddfd6f3`, `47d4c935`, `88b77623`, `cdd45ad2`, `4baa53c7`, `fa4fce58`,
`102f4dae`, `16029fa8`, `7bc0f9ca` R1), recorded (`85d150dc` → BUG-005,
`804f9588`/`5ce4d407` → BUG-041, `576a541f` → BUG-087, `a6a068ce` → BUG-004,
`60bbf466` → BUG-105/106/107, the I1 commits → BUG-098). October: 103
candidates, rows 1–56, DC01–DC19, trains 18–20 — same-branch
(`b5ab2f00`/`f5ef655e`, `46fc682c`, the seeded-heap rounds), coverage
(`241f7917` FR-36 dot-import `Intn` — a machine-stuck on an unmodeled
import, borderline), latitude/design (`59ac9431`, `8de727a5`, `553b981c`,
`e5619ade`), apparatus (the DC lanes, F5), recorded (`517f9883` → BUG-004,
`4f722dde` → BUG-118/121, the row-34/37/38/39 lanes → BUG-125–131).

## 4. Verdict

The classification is largely fit: 20 of the 25 shapes are cut by
mechanism, their axes name the functions and routes a lane would enumerate,
and the sample placements hold. The record is not complete, and two of the
gaps sit on the sweep's first page: S2's instance list is missing L1, L2a and
`923e3ec0`'s string conversions (F1, F3), and the plan's third slot holds a
tool-boundary shape in place of the core's absorbing defaults (F2, F5).

Step 2 should not start from this record as the complete index. What is
needed first, in the lane's own form (an entry per fix, status fixed,
Discovered: the commit, a Neighbourhood line): L1, L2a, L3 (F1; L10 at the
owner's word); `923e3ec0`'s two defects (F3); `31eeb6dd` with BUG-149's
sentence corrected (F4); a decision on the pre-index trio (F8) and on R15/E7
versus BUG-159 (F7); the core absorbing-default shape or its written
exclusion (F2); S24 moved out of Tier-1 slot 3 with the apparatus rule
settled (F5); BUG-138 with BUG-105 and DC07 as one byte-transparency
neighbourhood (F6); the member lists re-ordered or the sentence dropped
(F10). The S4 and S3 lanes (Tier-1 positions 1 and 3) are unaffected by the
omissions and can start now; S2's lane after F1/F3 land; the rest after the
owner's rulings on F2, F5, F7 and F8.

Reproduce: `scripts/check-bugs.sh` and `scripts/check-bugs.sh --list` in a
checkout of `d0c7631c` with `artifacts/coverage/{latest,negative-latest}.*`
present; the baseline lookups are `git show <hash>^:baselines/native-full.tsv
| grep -P '\t<row>\t'` for the rows named above; the count checks are a
script over `docs/defect-shapes.md`'s table rows and §3 member lists.
