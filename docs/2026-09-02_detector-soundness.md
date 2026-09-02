# Detector soundness: the -race differential, the footprint-gap probes, and the honest state of "racy → refused" (2026-09-02)

Lane: `t4-detector-soundness` (fidelity work program Tier 4; decision
1's named owner for detector completeness — `docs/assessment/
decisions-2026-08-31.md` item 1; outsider review D5 "the best
value-per-cost item"; A1-07's REOPEN and A2-Q3's circular delegation
both land here). Base commit e7d07b26; oracle pin go1.26.5. Everything
below is [AGENT]-executed and [AGENT]-judged inside the [USER]-approved
mandate; the one ruling it implements is Q-RACEPATH (RULED [USER]
2026-08-31, §4). One item returns to the [USER]: the Q-ATOMIC owner
proposal (§6), onto which BUG-080's fix is sequenced by [AGENT]
judgment (§3.2 — the fix is separable, so the sequencing is
revisable). Q-U5 (§3.3) was posed by this report's first draft and
WITHDRAWN at the pre-merge audit (B1): its exhibit is racy under
go_mem.

Audit fix round (2026-09-02; the pre-merge adversarial audit's
B1/B2/S1–S10/NOTEs, commits in §7): the runner was hardened (§2's
cell list gained `possible-HOLE`, `gc-no-verdict`, `refused`; exit
codes now carry every loud cell) and the corpus leg was RE-RUN at
the tip — §2 carries the corrected matrix, with the first run's
numbers kept beside it where they are the derivation anchor.

Tool: `scripts/detector-soundness` (lane tooling — writes only
`artifacts/detector-soundness/`, touches no gate, no baseline).
Evidence: `docs/evidence/2026-09-02_detector-soundness/`.

---

## 1. What was measured, and what the four cells mean

For every in-scope case two race verdicts were obtained and crossed:

- **gc side.** The SAME `tools/coverageharness` binary the differential
  gate runs, built with `-race`, executed 5× at GOMAXPROCS=1 and 5× at
  GOMAXPROCS=8. A run is RACE iff TSan printed `WARNING: DATA RACE`.
  gc verdict = RACE if any of the 10 runs is red, else **DRF-in-10** —
  a per-run sampler's verdict, reported as counts, never a proof.
- **machine side.** The schedule ENUMERATOR (`golean
  coverage-observations`, the enumerating lanes' engine) run WITHOUT
  `--expect-status`, so every member's status is visible: **RACE-ALL**
  (every enumerated registry-point path refuses), **RACE-SOME** (some
  paths refuse — a schedule-dependent race), **DRF** (no path refuses),
  or **ENUM-FAIL:<cause>** (budget / timeout / a member class the bare
  enumerator refuses — the row is then UNCERTIFIED, never silently
  DRF). The default stream's single run is recorded beside it: that is
  the per-run verdict the strict lane actually sees.

| cell | meaning |
|---|---|
| agree-race | gc RACE ∧ machine RACE-ALL/SOME |
| agree-DRF | gc DRF-in-10 ∧ machine DRF |
| **HOLE** (third cell) | gc RACE ∧ machine DRF — the soundness hole named by the mandate: SC semantics given to a program TSan races. Every row is diagnosed by hand below; the raw count is reported as-is. |
| over-refusal (fourth cell) | gc DRF-in-10 ∧ machine RACE-* — the three-way investigation rule (diff-coverage: too-eager detector / a schedule the sampler never hit / misclassified program) |
| uncertified | gc DRF-in-N or NO-VERDICT ∧ machine ENUM-FAIL — listed with cause and the single-run status |
| **possible-HOLE** (audit B2) | gc RACE ∧ machine ENUM-FAIL — a TSan-red program the enumerator could not certify either way; loud and exit-bearing, never filed as "uncertified" (the first runner did exactly that on the two BUG-080 pins, whose params omitted `sites=`, and exited 0) |
| gc-no-verdict (audit S3) | gc produced no COMPLETED run (all timed out or died before an outcome) ∧ machine DRF/RACE-* — never counted as agreement |
| refused (audit B2) | an enumerating-lane row whose params omit `width=`/`sites=` — the runner invents no bound; exit-bearing |

Since the audit fix round the machine verdict is also REFUSED (an
`ENUM-FAIL`) when the enumerator's stats report truncation
(`nonterm=`/`backedgeCapped=` > 0), when any member's status is
outside {ok, panic, race} (only `race` is a refusal), or when the
default-stream single run is outside that set (S1/S3); and the gc
verdict is `DRF-in-N` only if at least one run COMPLETED (exit 0, or
a transcript showing the program's own outcome — an observation, a
`panic:` or a `fatal error:` line).

Scope of the corpus leg, at the base commit: all 21 racy + 26
membership + 58 confluent rows, plus the 252 strict-lane rows whose
feature tags touch goroutines/channels/sync/select/mutex/rwmutex/
waitgroup/deadlock/race/atomics — 357 rows (the strict rows are the
ones the gate never grades for races at all: their default stream
plus three variant streams must merely not refuse). At the branch tip
the in-scope set is **364**: racy 25 (21 + the 2 Q-RACEPATH racy
guards + the 2 BUG-080 pins), membership 26, confluent 61 (58 + the 2
Q-RACEPATH chain-form guards + `race/free/array-read-write`, which
MIGRATED strict→confluent with its FAIL→PASS flip — that is the
confluent "+1" between this paragraph and the tables below), strict
252 (−1 migrated, +1 `race/free/array-dyn-index-read-write`, the
born-FAIL residual pin, which carries no lane column). Probe leg: 45
novel subjects (§3).

---

## 2. The corpus matrix

### 2.0 The first run (5da5d8ff's record) and its corrections

Run: `corpus.summary.txt` / `corpus.matrix.tsv` / `corpus.meta.tsv`
(2026-09-02T00:22–00:39Z, post-Q-RACEPATH machine; **362 of the 364
in-scope rows at the tip** — the 357 in-scope rows at the base commit
plus the 5 Q-RACEPATH rows; the 2 BUG-080 pins post-date this run and
ARE the third cell (§3.2) — the first draft's "no exhibit in the
corpus" was true only of this 362-row snapshot). 10 `-race` runs per
row (5 × GOMAXPROCS=1, 5 × GOMAXPROCS=8); strict rows enumerated under
`width=4,sites=32,cap=512,work=4000000,backedge=1`, enumerating-lane
rows under their own `params` (with the first runner's silent
`sites=8` default where a row omitted it — audit B2).

| cell | rows as recorded | corrected (audit S1) |
|---|---|---|
| agree-race | **23** — racy 23 (21 at base + the 2 `race/negative/array-const-index-*` guards), TSan red **10/10 on every one** at both GOMAXPROCS values; machine RACE-ALL on every one | 23 |
| agree-DRF | **276** — strict 191 · confluent 60 · membership 25 | **275** — `goroutines/send-then-spin` (membership) was filed agree-DRF with `nonterm=200` truncated paths and a `fuel-out` single run; under the fix round's rule that is `ENUM-FAIL:truncated`, i.e. uncertified |
| **HOLE** (gc red, machine DRF) | **0** | 0 of these 362 (the 2 pins outside the snapshot are HOLEs — §2.2) |
| over-refusal | **1** — strict 1: `race/free/array-dyn-index-read-write`, the O1 dynamic-index residual, by design (§4) | 1 |
| uncertified (machine ENUM-FAIL) | **62** — strict 60 · confluent 1 · membership 1, every one gc DRF-in-10 | **63** (+ send-then-spin) |

The 62 uncertified rows of the record, by cause (single-run status in
brackets):

| cause | rows | what it means |
|---|---|---|
| deadlock members — the enumerator refuses deadlocking members by design | 20 [deadlock] | the deadlock lane's rows; under `-race` gc's deadlock detector is suppressed, so all 200 of their gc runs TIMED OUT (15 s) — the first runner still filed them `DRF-in-N`; under the corrected runner that is gc `NO-VERDICT` (no completed run), and the cell stays `uncertified` |
| frontier refusals (`unsupported`: frontend-quarantined / atomics / Cond / TryLock / Goexit / init-spawn) | 24 [unsupported] | standing FAIL rows of the baseline; nothing to grade — the refusal IS the verdict |
| fatal members — the enumerator refuses runs ending in a `fatal` | 7 [fatal] | the sync-misuse fatal rows (unlock-of-unlocked, RUnlock misuse, nil-func spawn); their single default-stream run is the fatal |
| enumeration budget (sites/width/backedge) | 11 [ok] | pipelines, worker pools, prime sieves, the select-select loop, a goose spawn row — re-run deeper in `corpus-deep` (§2.1) |

So on this 362-row snapshot the third cell is empty and the 63 rows
the enumerator could not certify are all rows where gc found no race
in 10 runs either (20 of them with NO completed gc run at all);
"uncertified" is their honest label. The strict-lane concurrency
rows — which the gate never grades for races — got 191 doubly
checked (agree-DRF) and 60 checked on the gc side ONLY (uncertified
with cause) — not "each doubly checked", as the first draft said.

### 2.1 The deep re-enumeration of the 11 budget-limited rows

Re-run (`corpus-deep.*`) with `width=8,sites=96,cap=1024,
work=30000000,backedge=1` and a 900 s enumeration budget: **2 more
rows certified agree-DRF** (`imported-goose/unittest/spawn/simple-
spawn`, `spec-examples-stmt/go-statements/func-literal` — both with
`backedgeCapped=0` and no `nonterm=`, so they stand under the fix
round's truncation rule); **9 remain uncertified** — 5 enumerations
TIMED OUT at 900 s (`goroutines/
pipeline/{two-stage,buffered-stage}`, `goroutines/worker-pool/{sum,
shared-feed}`, `sync/waitgroup-workers-join/workers-join` — the
multi-worker pool shapes whose registry-point trees are large by
nature), the two prime sieves exceed 96 consumption sites, the goose
`parallel-search-replace` row REFUTES width 8 too (site bound 9 — a
pool of 9 runnable goroutines), and `channels/select-select/beside-
loop` hits the Q-SELSEL refusal on some paths (a standing frontier
row). All 9 are gc DRF-in-10 and their single default-stream run is
`ok`; they are recorded as UNCERTIFIED-by-budget — the honest
residual of class (ii) in §5. Totals of the 362-row snapshot: BEFORE
the deep re-run agree-DRF 275 / agree-race 23 / HOLE 0 / over-refusal
1 / uncertified 63 (20 deadlock members, 7 fatal members, 24 frontier
refusals, 11 budget, 1 truncated); AFTER it agree-DRF **277** /
agree-race 23 / HOLE 0 / over-refusal 1 / uncertified **61** (20
deadlock, 7 fatal, 24 frontier, 9 budget, 1 truncated). (The first
draft carried 278/60 — before audit S1 moved `send-then-spin` out of
agree-DRF.) The corrected, complete matrix at the tip is §2.2.


---

## 3. The footprint-gap probes (45 subjects; `probes/`, `probes.tsv`)

Families: **U2** (7 — `len`/`cap` on channels and the other `len`
forms), **U4** (6 — the sync primitives' own words), **U5** (2 —
cross-goroutine unlock), **footprint hunt** (27 — one `stepAccesses`
arm or O1 shape each, chosen for what the corpus does NOT pin: struct
copy / boxing / send-operand copies, defer-time argument reads, method-
value receiver copies, tuple swaps, `copy`/`append` element traffic,
array slicing, pointer-to-array elements, the O1 constant/dynamic index
forms in both chain orders, slice/array range, select send operands,
receive-target stores (immediate and woken), globals, captures, map
disjoint keys, `[]byte(s)`, spawn arguments, nested field paths),
**schedule** (3 — races that exist only on some schedules).

Post-fix run (`probes-post.summary.txt`): **agree-race 24 · agree-DRF
12 · HOLE 2 · over-refusal 3 · uncertified 4**. Pre-fix run
(`probes-pre.summary.txt`): agree-race 22 · agree-DRF 8 · HOLE 2 ·
over-refusal 4 · uncertified 9. The pre→post join (audit S10: the
two matrices joined on id) has exactly SEVEN movers — Q-RACEPATH
(§4) moved two: `footprint/{array-const-index-field,field-array-
const-index}-vs-write` over-refusal→agree-DRF; the other five left
`uncertified` because the post run's `--strict-enum` gained
`backedge=1` and the loop probes were re-parametrized (`backedge=
full`): `footprint/range-array-vs-elem-write` → agree-race,
`footprint/range-slice-disjoint-vs-write` → agree-DRF,
`schedule/tail-race` → agree-race, `schedule/deep-path-race` →
**over-refusal** (not an agreement: the schedule-dependent race the
sampler never hit, §3.4), `u5/handoff-unlock` → agree-DRF. Net:
agree-race +2, agree-DRF +4, over-refusal −2 +1, uncertified −5.
(Under the fix round's runner the 4 remaining `uncertified` probes —
three U4 fatal-member rows and `u5/cross-unlock-publish` — are all gc
RED and therefore land in `possible-HOLE`; §3.2/§3.3 diagnose each;
the re-run is `probes-tip.*`, §2.)

### 3.1 The footprint arms probed agree with gc in both directions (a sample of 34, not a census)

All 27 footprint-hunt probes plus the 7 U2 probes landed in the two
agreeing cells except the single O1 residual (below). In particular
the shapes most likely to hide a hole did not: the receive-into-a-
shared-variable store (immediate AND woken-receiver forms — the target
store rides `enterRecvTargets` → `storeK` → `storeTargetAccess`, so a
registry op's store IS footprinted), the method value's receiver copy
(spec §Method values: saved at creation — the machine reads it there),
defer-time argument reads, select send-operand reads, range over an
array value (copied at range start — both sides red), `a[:]` on an
array local (address formation — both sides green), `len(a)` on an
array (a constant — both sides green; the frontend folds it). U2 is
CONFIRMED benign on the pinned toolchain: `len(ch)`/`cap(ch)` beside a
concurrent send/close are TSan-green (uninstrumented, probe p26's
claim re-verified 10/10 each) and machine-DRF; every OTHER `len`/`cap`
form that reads a variable (slice/string header, map object) is red on
both sides.

### 3.2 The third cell is exactly U4 — now BUG-080, born-FAIL pinned

Five U4 probes are TSan-red 10/10 at both GOMAXPROCS values:
`struct-overwrite-vs-lock`, `wg-overwrite-vs-add`,
`rw-overwrite-vs-rlock`, `once-overwrite-vs-do`, `struct-copy-vs-lock`;
the control `disjoint-field-vs-lock` (a sibling-field write beside the
lock) is agree-DRF, so the class is precisely the primitive's own state
words. TSan's reports name them: `Write … sync/atomic.
CompareAndSwapInt32` (Lock's CAS on `m.state`) vs the copy's read;
`Read … runtime.raceread` inside `WaitGroup.Add` vs the overwrite. The
machine records NO access for a sync op (Race.lean classifies the sync
cell's traffic as SYNCHRONIZATION), so the plain copy/overwrite has
nothing to conflict with: two probes ran to a value (machine DRF — the
HOLE cell), three are UNCERTIFIED only because their overwrite makes a
later Unlock/RUnlock/onceComplete a FATAL member and the bare
enumerator refuses runs that end in a fatal (their single default-
stream runs are `ok`; gc red regardless).

Honest classification: by mem#restrictions a non-atomic access beside
an atomic one IS a data race, so these programs are racy by the spec
and the machine gives them SC value semantics — the DRF-SC premise does
not cover them. It is the misuse class only (vet's `copylocks` flags
every shape; no race-free program is touched), it was RECORDED as U4
since spec-parity slice 2, and it is now **BUG-080** with two born-FAIL
racy-lane pins (`race/negative-sync/{wg-overwrite,mutex-copy}` — the
racy lane's oracle is `-race`, which is red 10/10 on both). Fix shape:
NOT a table entry — recording sync ops as plain writes would make two
legal contending Locks conflict; what gc realizes is a third access
KIND: `RaceAccess := Kind × Loc`, atomic↔atomic non-conflicting,
atomic↔plain conflicting, one atomic access recorded at the sync
cell's path from `raceUpdate`'s sync arm.

**Sequencing — an [AGENT] judgment, not a forced dependency** (audit
S4 corrected the first draft, which wrote the deferral as if the arc
were a prerequisite). The access kind is SEPARABLE from the
sync/atomic LOWERING the atomics arc builds (S–M) and could land as
its own slice. It is sequenced to ride that arc's detector wave
(`docs/2026-09-01_qatomic-owner-proposal.md` §4) for two stated
reasons: (i) each primitive is ONE `syncData` cell, so an atomic
access at the cell's path must be checked against the `locPrefix`
over-refusal (the `disjoint-field-vs-lock` control — a sibling-field
plain access beside the lock — must stay green) and reconciled with
the `wgSemaAccess` carve-out, which already records one PLAIN pair on
that very cell; (ii) gc's per-primitive instrumentation differs
(WaitGroup runs its state accesses under `race.Disable` and exposes
the `wg.sema` pair; Mutex exposes its state CAS as an atomic), so the
per-op recorded set has to be derived primitive by primitive from
`-race`'s realized set — the alignment pass the atomics arc performs
anyway. Revisable: if the arc slips, the kind becomes its own S
slice. Recorded against decision 1's deferred investment, as the
mandate directs; the same text is at Race.lean's U4 entry (comment
only), BUG-080's Fix-shape paragraph and the owner proposal §4.

### 3.3 The U5 probe is RACY under go_mem — Q-U5 WITHDRAWN (audit B1); the U5 class itself stands as recorded, unmeasured here

`probe/u5/cross-unlock-publish` (the Tests/GoCoreEval.lean
`syncXUnlockMain` shape as Go source: main holds the lock, spawns W1
— an owner-free unlocker — and W2 — locker-reader — BEFORE publishing
`g = 1`, unlocks, re-locks; W1 unlocks; W2 locks and reads `g`) is gc
`-race` RED in 7/10 runs and machine `ok` on the default stream. This
report's first draft read that as TSan over-reporting a go_mem-DRF
program ("main's Unlock is call 1, W2's Lock is call 3, so the read is
ordered") and posed ruling Q-U5 — keep the memory-model merge vs
align to TSan's overwrite-Release. **That reading was wrong; the
pre-merge audit refuted it (B1), and the refutation was re-verified
at this fix round.**

The refutation. mem#locks numbers Unlock/Lock calls PER EXECUTION,
and this program has executions numbered differently from the one
the draft assumed. In the (non-fatal) execution where W1's owner-free
Unlock is Unlock call 1 and W2's Lock is Lock call 2 — W2 now holds
the lock — main goes on to write `g = 1` and perform Unlock call 2
(legal: "a locked Mutex is not associated with a particular
goroutine"), whose n<m successor is Lock call 3 = main's own re-Lock,
NOT W2's Lock (2 ≮ 2). Nothing orders main's write before W2's read:
a real data race under go_mem, not an oracle artefact. Every
TSan-red run is this execution. The machine agrees: on the probe's
wire, `native-json-run --choices 1,1,0,1,1` and `--choices 1,1,2,1,1`
both report `status:"race"` (re-run at this fix round; the auditor's
tape histogram to length 6 is ok 448 / fatal 586 / race 59). The
draft's fatal-path explanation was INVERTED as well: the W1-before-
main ordering is the LEGAL racy path; the fatal members are the tapes
on which two Unlocks are adjacent ("unlock of unlocked mutex"). The
first runner filed the row "uncertified" because those fatal members
make the bare enumerator refuse; under the corrected runner a gc-red
row the enumerator cannot certify is `possible-HOLE` (§2), and this
one's diagnosis is: a racy program, refused by the machine on the
racy paths — no hole.

**Ruling record — Q-U5 WITHDRAWN** ([USER] ruling, recorded by the
[AGENT] fix round at the auditor's finding: "posed on a refuted
premise; withdrawn at audit B1"). Nothing returns to the [USER] from
this section. The withdrawal is carried to the doctrine register #4
(iii), the inventory C10 EVIDENCE bullet and the evidence README,
which had listed Q-U5 as pending.

What stands, undisturbed. The U5 CLASS in Race.lean (`syncRelease`
is a merge-join; gc's TSan hook is the overwrite `race.Release` —
Race.lean's U5 entry) is a real, pre-existing modelling difference;
this lane neither exhibited nor refuted it. The auditor's correct
exhibit shape needs a THIRD goroutine holding the lock while the
owner-free unlock happens: main `Lock; g = 1; Unlock` — W2 `Lock`
and HOLD — W1 owner-free `Unlock` — W3 `Lock; read g`. There W3's
Lock (call 3) follows both main's Unlock (call 1) and W1's (call 2)
under n<m, so go_mem orders the read, while TSan's overwrite leaves
semA carrying W1's clock and reports. The structural fact that keeps
this out of the corpus: it CANNOT be made deterministic — any
synchronization that orders W1 after W2's Lock (to exclude the racy
numbering above) hands W1 main's clock through that edge, which
collapses overwrite to merge and TSan agrees with the machine again.
That is exactly why Race.lean calls U5 un-lane-able (the mixed-oracle
class). It remains recorded, not measured.

The eval pin. `Tests/GoCoreEval.lean` `syncXUnlockMain` — the pin
this probe transcribed — is the SAME racy shape. What it records is
that the default-stream run (main publishes, unlocks and re-locks
before W1's unlock) yields `1` under the merge release and would
refuse under the overwrite release (mutation-tested). It does NOT
record what this section first claimed — a go_mem-DRF program that
TSan reports; its docstring's "TSan-red/ours-green" gloss is TSan's
red on the OTHER, racy execution of a racy program. The pin itself
is untouched by this round (Tests/ is outside the round's edit set);
correcting its docstring is recorded here as owed to the next
Race.lean-touching slice. The control `handoff-unlock` (W1 receives
a signal sent after the publish) is agree-DRF on both sides.

### 3.4 The over-refusal cell: one by design, two that show the per-run nature

- `array-dyn-index-vs-write` — the O1 dynamic-index RESIDUAL the
  Q-RACEPATH ruling deliberately left (§4); gc green 10/10, machine
  RACE-ALL. By design, pinned `race/free/array-dyn-index-read-write`.
- `schedule/default-path-race`, `schedule/deep-path-race` — the race
  exists only on the child's default path (one or two lost polls).
  gc: **0/10 red** at both GOMAXPROCS values — the sampler never
  realized the racy schedule. Machine: RACE-SOME (1 of 2 members
  refuses). Three-way rule outcome (b): a schedule the sampler never
  hits — the ENUMERATOR is the stronger instrument here, and this is
  the concrete face of "per-run": `go run -race` proves a race only
  when its schedule co-executes the pair; ten runs proved nothing
  about these two programs, the enumeration did.

### 3.5 What the probes did NOT find

No `stepAccesses` arm was found missing for any plain-data access
shape tried (27/27 hunt probes agree, the receive-target stores
included); no U2 form is fail-open against `-race` on go1.26.5; the
Q-RACEPATH narrowing does not over-reach (`array-const-index-same-elem`
and `-vs-whole-write` are red on both sides). The probe set is a
sample, not a census — the lockstep obligation (every new access-
bearing `stepFn` arm adds its footprint arm) remains the standing
completeness discipline, and `scripts/detector-soundness` is now the
cheap re-check for any footprint-touching change.

---

## 4. Q-RACEPATH — implemented (RULED [USER] 2026-08-31, row 4)

`GoLean/GoCore/Race.lean`: `fieldChainTarget` → `projChainTarget
(s : ExecState)`. The narrowing chain now passes through an `indexGet`
frame whose pending index is an `Expr.intLit` (go/types folds every
constant index expression to one; constant indices are compile-time
bounds-checked) PROVIDED `loadLoc s loc` yields an ARRAY — element
paths live under the array's own `Loc`, exactly where element STORES
land, so a constant-index read and a disjoint-element write are
disjoint paths; a slice/string variable's cell is a HEADER whose
elements live elsewhere and its read stays whole-cell (the element read
is `strictOpAccesses`' job). Chains compose in either order (`a[1].x`,
`s.arr[1]`). Dynamic indices stay whole-cell — O1's residual, with the
re-open trigger (memo §4 option (B), deferred-footprint recording,
only if a real target needs dynamic-index disjointness on a value-path
array; raft indexes slices, already precise).

Flip evidence (`scripts/coverage run`, this tip):

| row | before | after |
|---|---|---|
| `race/free/array-read-write` (the BUG-041 red pin) | FAIL lean-observation (`race`) | **PASS confluent** — \|set\|=1 certified over all schedules |
| `race/free/array-const-index-field` (new, `a[1].x`) | — (probe: over-refusal) | PASS confluent |
| `race/free/field-array-const-index` (new, `s.arr[1]`) | — (probe: over-refusal) | PASS confluent |
| `race/negative/array-const-index-same-elem` (new) | — | PASS racy — every path refuses |
| `race/negative/array-const-index-whole-write` (new) | — | PASS racy — every path refuses |
| `race/free/array-dyn-index-read-write` (new residual pin, `a[i]`) | — | FAIL lean-observation (`race`) — born-FAIL on BUG-041's Cases line |

Ruling text carried to: inventory C10 (O1 sentence), ledger §6
Q-RACEPATH row + the mem#restrictions row, BUG-041 (NARROWED; residual
pinned), the ruling sheet row 4 (IMPLEMENTED), Race.lean O1 +
`projChainTarget` docstrings.

---

## 5. Register #4 — the honest state of "racy → refused"

The rewrite landed in the doctrine (`docs/2026-08-11_essence-of-go-
doctrine.md` register #4) and the inventory (C10's EVIDENCE bullet);
this is its argument.

**What is DETECTED.** The detector is HB-complete per run by
construction: `raceUpdate` folds every private step's footprint under
the goroutine's current vector clock, so if two conflicting accesses
by different goroutines execute in a run and no realized HB edge
orders them, the run refuses — regardless of how adversely they were
interleaved (the FastTrack epoch subsumption makes the check
interleaving-insensitive within a run). Measured: 23/23 gc-red corpus
rows refuse on every enumerated path; 24/24 gc-red plain-data probes
refuse on every path; the receive-target stores, method-value copies,
defer-time reads, select operands, range copies, `copy`/`append`
traffic and nested paths all footprint where gc reads/writes.

**What is NOT detected — three classes, each with its evidence.**

1. *The sync primitives' own state words* (U4 → BUG-080). Racy by
   mem#restrictions (non-atomic beside atomic), TSan-red 10/10, run
   to a value here. Misuse-only (vet copylocks); pinned born-FAIL;
   fix = the atomic access kind (atomics arc). This is the ONE class
   where "SC semantics given to a racy program" is literally true
   today, and it is now on the books as such.
2. *Schedule-dependent races the enumeration never realizes.* The
   refusal is per-RUN; the program-level claim is exactly the
   enumerator's reach. Where the enumerator certifies (racy lane's
   every-path claim, confluent/membership full enumerations, and now
   the strict concurrency rows this lane enumerated) the claim is
   mechanical; where it cannot (62 corpus rows: deadlock/fatal
   members, frontier refusals, budget) the row is UNCERTIFIED and the
   strict gate's one-default-stream run is all that grades it. The
   probes show the sampler side of the same coin: two racy programs
   TSan never caught in 10 runs. Neither instrument is a per-program
   oracle; the enumerator is the stronger one where it runs.
3. *Footprint approximations*, each measured except one: U2 benign
   (7/7); O1 fail-closed (over-refusal, 1 residual pin, Q-RACEPATH
   done); U5 NOT measured — the probe meant to exhibit it is racy
   under go_mem and the machine refuses its racy paths (Q-U5
   withdrawn at audit B1, §3.3); the merge-vs-overwrite Release
   difference stands as Race.lean records it, un-lane-able because
   its exhibit cannot be made deterministic; U1/U3 closed earlier
   and re-confirmed by the corpus rows that pin them.

**What the per-run wording promises.** Every run on which a
conflicting pair co-executes refuses. Nothing about runs where it does
not; nothing about registry-granularity vs full interleaving (the
NPDRF conjecture, register #5, decision 1's deferred proof
investment — where class 2's residual and BUG-080's proper statement
both belong).

**Guard added (A1-07's (S) item) — what the runner actually checks
(audit B2 corrected the first draft's "the runner IS the check").**
No gate guard was added this lane (the mandate excluded gate
changes). `scripts/detector-soundness --select in-scope` is a
re-check that must be RUN and READ: its exit code is its verdict on
its own matrix — 1 on any HOLE or possible-HOLE row, 2 on an
incomplete matrix (refused / gc-infra / unclassified rows, a died
worker, an `--id` matching nothing) — and it compares against no
recorded HOLE list. While BUG-080 is open the standing run exits 1
with exactly its two pins in HOLE; the discipline after a footprint-
touching change is to re-run and compare the HOLE / possible-HOLE
rows against BUG-080's Cases: line by hand — a row not on a BUGS.md
Cases: line is a STOP. The first runner did not meet even this bar:
it exited 0 on the two BUG-080 pins (their params omitted `sites=`,
the runner defaulted to 8, the enumeration hit the bound, the rows
were filed "uncertified"); the fix round gave RACE∧ENUM-FAIL its own
exit-bearing cell, made the runner refuse rows without a declared
bound, and declared `sites=` on every enumerating-lane row (the two
pins at 32, the rest at the manifest's documented default 8, gate-
neutral). Making concurrency-tagged rows declare a lane reason is
recorded as a follow-up, not done (a manifest-gate change).

---

## 6. Q-ATOMIC owner proposal (rider)

`docs/2026-09-01_qatomic-owner-proposal.md` — returns row 2 to the
[USER] with the two refreshes the sheet demanded: the FairStream tier
is FUTURE WORK TO BE BUILT (no `Fair`/`FairStream` Lean definition
exists anywhere; the quantifier is reasoning-side post-split; this
repo's executable analogue is the existing `nonterm=` membership
accounting, with NO termination claim), and an owner (a semantics-repo
lane for the machine half; the reasoning repo for the Fair-quantified
claim class). Options: **ratify A′ with this owner** (recommended) or
**defer the family**; memo option (A) "tier bundled" is recorded as not
available post-split. BUG-080's fix (the atomic access kind) is
sequenced onto this arc by [AGENT] judgment (§3.2 — separable, two
stated reasons, revisable), which raises the arc's priority one
notch; if the arc is deferred, the kind becomes its own S slice.

---

## 7. Commits on this branch (per item)

1. `05d0ec54` — lane TOOLING + PROBES: `scripts/detector-soundness`
   (the runner), the 45 probe subjects, the probe manifest, the pre-
   and post-Q-RACEPATH probe records. Lane tooling + evidence only.
2. `653319b6` — the Q-ATOMIC owner-proposal memo (docs only, §6).
3. `804f9588` — Q-RACEPATH implemented + BUG-080 pins + baseline
   re-pin [TRUST-ADJACENT: one `Race.lean` footprint change]: the
   `projChainTarget` narrowing, 6 corpus rows (1 flip, 4 born-PASS
   guards, 1 born-FAIL residual pin) + 2 born-FAIL U4 pins, BUG-041
   NARROWED / BUG-080 opened, ledger §6/§8 + rulings sheet row 4 +
   inventory C10 (O1 sentence, measured EVIDENCE bullet). Gate: full
   `ci --diff` at that tip (drift = exactly the 8 rows in the baseline
   header, no PASS→non-PASS flips), then `ci` PASS against the
   re-pinned baseline. The baseline's `# cases:` line moved 2521→2533
   for 7 added rows: the extra 5 correct a prior stale-by-5 count
   (the 2026-09-01 gotest-fixes re-pin added 5 rows without updating
   the line); 2533 is the true row count at 804f9588.
4. `5da5d8ff` — the report, register #4's measured rewrite (doctrine),
   the corpus/corpus-deep evidence records and the evidence README.
5. Audit fix round (2026-09-02, the pre-merge adversarial audit —
   B1/B2/S1–S10/NOTEs), per item: (a) runner hardening + `sites=`
   declared on every enumerating-lane row [lane tooling + corpus
   metadata]; (b) Race.lean U4 comment (sequencing wording, comment
   only) + BUGS.md + owner-proposal edits [records]; (c) this report,
   doctrine register #4, inventory C10, evidence README — Q-U5
   withdrawn, scope sentences and counts corrected [records]; (d) the
   re-run at the tip: `corpus-tip.*` / `probes-tip.*` evidence, the
   corrected matrix in §2, the gate tail under
   `docs/evidence/2026-09-02_detector-soundness/gate-tail.txt`.

Gate tail at the branch tip is under the evidence dir
(`gate-tail.txt`) and pasted in the lane's end report; the baseline
header names every moved row and its reason.
