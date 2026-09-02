# Detector soundness: the -race differential, the footprint-gap probes, and the honest state of "racy → refused" (2026-09-02)

Lane: `t4-detector-soundness` (fidelity work program Tier 4; decision
1's named owner for detector completeness — `docs/assessment/
decisions-2026-08-31.md` item 1; outsider review D5 "the best
value-per-cost item"; A1-07's REOPEN and A2-Q3's circular delegation
both land here). Base commit e7d07b26; oracle pin go1.26.5. Everything
below is [AGENT]-executed and [AGENT]-judged inside the [USER]-approved
mandate; the one ruling it implements is Q-RACEPATH (RULED [USER]
2026-08-31, §4). Two items return to the [USER]: BUG-080's fix
sequencing (rides Q-ATOMIC, §3.2) and the new ruling Q-U5 (§3.3).

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
| uncertified | machine ENUM-FAIL — listed with cause and the single-run status |

Scope of the corpus leg: all 21 racy + 26 membership + 58 confluent
rows, plus the 252 strict-lane rows whose feature tags touch
goroutines/channels/sync/select/mutex/rwmutex/waitgroup/deadlock/race/
atomics — 357 rows (the strict rows are the ones the gate never grades
for races at all: their single default-stream run must merely not
refuse). Probe leg: 45 novel subjects (§3).

---

## 2. The corpus matrix

Run: `corpus.summary.txt` / `corpus.matrix.tsv` / `corpus.meta.tsv`
(2026-09-02T00:22–00:39Z, post-Q-RACEPATH machine; 362 rows — the 357
in-scope rows at the base commit plus the 5 Q-RACEPATH rows this lane
added; the 2 BUG-080 pins were added after this run and are measured
in the probe leg as `u4/wg-overwrite-vs-add` and `u4/struct-copy-vs-
lock`). 10 `-race` runs per row (5 × GOMAXPROCS=1, 5 × GOMAXPROCS=8);
strict rows enumerated under `width=4,sites=32,cap=512,work=4000000,
backedge=1`, enumerating-lane rows under their own `params`.

| cell | rows | by lane |
|---|---|---|
| agree-race | **23** | racy 23 (every racy-lane row: 21 at base + the 2 new `race/negative/array-const-index-*` guards) — TSan red **10/10 on every one** at both GOMAXPROCS values; machine RACE-ALL on every one |
| agree-DRF | **276** | strict 191 · confluent 60 · membership 25 |
| **HOLE** (gc red, machine DRF) | **0** | — |
| over-refusal | **1** | strict 1: `race/free/array-dyn-index-read-write` — the O1 dynamic-index residual, by design (§4) |
| uncertified (machine ENUM-FAIL) | **62** | strict 60 · confluent 1 · membership 1 — every one gc DRF-in-10 |

The 62 uncertified rows, by cause (single-run status in brackets):

| cause | rows | what it means |
|---|---|---|
| deadlock members — the enumerator refuses deadlocking members by design | 20 [deadlock] | the deadlock lane's rows; under `-race` gc's deadlock detector is suppressed, so all 200 of their gc runs TIMED OUT (15 s) — no verdict either way beyond "no race report before the hang" |
| frontier refusals (`unsupported`: frontend-quarantined / atomics / Cond / TryLock / Goexit / init-spawn) | 24 [unsupported] | standing FAIL rows of the baseline; nothing to grade — the refusal IS the verdict |
| fatal members — the enumerator refuses runs ending in a `fatal` | 7 [fatal] | the sync-misuse fatal rows (unlock-of-unlocked, RUnlock misuse, nil-func spawn); their single default-stream run is the fatal |
| enumeration budget (sites/width/backedge) | 11 [ok] | pipelines, worker pools, prime sieves, the select-select loop, a goose spawn row — re-run deeper in `corpus-deep` (§2.1) |

So on the corpus leg the third cell is EMPTY, and the 62 rows that
the enumerator could not certify are all rows where gc found no race
in 10 runs either; "uncertified" is their honest label — the
mandate's failure mode ("a racy program slips through with SC
semantics") has no exhibit in the corpus, and the strict-lane
concurrency rows — which the gate never grades for races — are now
each doubly checked (191 agree-DRF; 60 uncertified with cause).

### 2.1 The deep re-enumeration of the 11 budget-limited rows

Re-run (`corpus-deep.*`) with `width=8,sites=96,cap=1024,
work=30000000,backedge=1` and a 900 s enumeration budget: **2 more
rows certified agree-DRF** (`imported-goose/unittest/spawn/simple-
spawn`, `spec-examples-stmt/go-statements/func-literal`); **9 remain
uncertified** — 4 enumerations TIMED OUT at 900 s (`goroutines/
pipeline/{two-stage,buffered-stage}`, `goroutines/worker-pool/{sum,
shared-feed}`, `sync/waitgroup-workers-join/workers-join` — the
multi-worker pool shapes whose registry-point trees are large by
nature), the two prime sieves exceed 96 consumption sites, the goose
`parallel-search-replace` row REFUTES width 8 too (site bound 9 — a
pool of 9 runnable goroutines), and `channels/select-select/beside-
loop` hits the Q-SELSEL refusal on some paths (a standing frontier
row). All 9 are gc DRF-in-10 and their single default-stream run is
`ok`; they are recorded as UNCERTIFIED-by-budget — the honest
residual of class (ii) in §5. Corpus totals after the deep run:
agree-DRF 278 / agree-race 23 / HOLE 0 / over-refusal 1 / uncertified
60 (20 deadlock members, 7 fatal members, 24 frontier refusals, 9
budget).


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
over-refusal 4 · uncertified 9 — the delta is Q-RACEPATH (§4: two
chain-form probes over-refusal→agree-DRF) plus the loop probes
re-parametrized with `backedge=full` (five uncertified→certified).

### 3.1 Every footprint arm probed agrees with gc in BOTH directions

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
KIND (atomic, conflicting with plain accesses only), which is the
atomics arc's detector deliverable (`docs/2026-09-01_qatomic-owner-
proposal.md` §4). Recorded against decision 1's deferred investment,
as the mandate directs.

### 3.3 The other gc-red / machine-not-red row is U5 — an ORACLE-vs-spec divergence, posed as ruling Q-U5

`probe/u5/cross-unlock-publish` (the Tests/GoCoreEval.lean
`syncXUnlockMain` shape as Go source): main holds the lock, spawns W1
(owner-free unlocker) and W2 (locker-reader) BEFORE publishing `g = 1`,
unlocks, re-locks; W1 unlocks; W2 locks and reads `g`. gc `-race`:
RED in 7/10 runs (TSan reports the read of `g` by W2 against main's
write — its overwrite-Release by W1 dropped main's clock). Memory
model: "for n < m, call n of l.Unlock() is synchronized before call m
of l.Lock() returns" — unconditional; main's Unlock is call 1, W2's
Lock is call 3, so the read IS ordered and the program is DRF by the
spec. The machine's merge release realizes the sentence (single run
`ok`; the enumerator is uncertified here because the paths where W1
unlocks before main's own Unlock are FATAL members — "unlock of
unlocked mutex" — which the bare enumerator refuses; the machine-side
record of the divergence is the eval pin). The control
`handoff-unlock` (W1 receives a signal sent after the publish) is
agree-DRF on both sides.

So this row is gc-RED / machine-not-red, but it is NOT "SC given to a
racy program": it is TSan over-reporting a go_mem-DRF program. It does,
however, contradict register #13's letter ("the refusal boundary is
TSan's REALIZED edge set") at exactly one point — the only place the
detector follows go_mem over TSan. Two coherent positions, for the
[USER]:

- **Q-U5 option (i) — keep the memory-model merge (current).** The
  machine refuses fewer programs than `-race` on this one shape; the
  divergence stays recorded (Race.lean U5, the eval pin, this report),
  register #13's sentence gains the qualifier "except U5, where the
  machine follows the memory-model sentence". Fail-open only relative
  to the ORACLE, never relative to Go.
- **Q-U5 option (ii) — align to TSan (overwrite Release).** Kills the
  divergence and makes the boundary literally TSan's; refuses a
  spec-DRF program (fail-closed direction); effort S (one `syncRelease`
  arm + the eval pin + a racy-lane row that could then be a corpus
  pin). The register #13 doctrine as written recommends this.

[AGENT] recommendation: (i) until a consumer needs TSan-exactness at
this shape — owner-free unlocks with no handoff are rare and vet-
adjacent — with (ii) recorded as the S-cost switch. Not decided here.

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
3. *Footprint approximations*, now each measured: U2 benign (7/7);
   O1 fail-closed (over-refusal, 1 residual pin, Q-RACEPATH done);
   U5 an oracle-vs-spec divergence (Q-U5 posed); U1/U3 closed
   earlier and re-confirmed by the corpus rows that pin them.

**What the per-run wording promises.** Every run on which a
conflicting pair co-executes refuses. Nothing about runs where it does
not; nothing about registry-granularity vs full interleaving (the
NPDRF conjecture, register #5, decision 1's deferred proof
investment — where class 2's residual and BUG-080's proper statement
both belong).

**Guard added (A1-07's (S) item).** None mechanical this lane: the
runner IS the check — a footprint-touching change re-runs
`scripts/detector-soundness --select in-scope` and any new HOLE row
is a STOP. Making concurrency-tagged rows declare a lane reason is
recorded as a follow-up, not done (it is a manifest-gate change and
the mandate excluded gate changes).

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
available post-split. BUG-080's fix (the atomic access kind) rides the
same arc, which raises its priority one notch.

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
   re-pinned baseline.
4. this commit — the report, register #4's measured rewrite (doctrine),
   the corpus/corpus-deep evidence records and the evidence README.

Gate tail at the branch tip is pasted in the lane's end report; the
baseline header names every moved row and its reason.
