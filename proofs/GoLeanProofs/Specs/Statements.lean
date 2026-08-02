import GoLeanProofs.Surface
import GoLeanProofs.Specs.QuorumTargets
import GoLeanProofs.Specs.GoldenQuorum
import GoLeanProofs.Specs.GoldenProgram

/-!
# The Iris-free statement layer (comparator-judge sprint, 2026-08-02)

Every definition a designated headline theorem's STATEMENT references must
live in a module whose transitive imports never touch `Iris.*` — that is the
deletion-test doctrine (`docs/2026-08-01_tcb-and-layering-doctrine.md`) made
visible in MODULE STRUCTURE, and it is what lets an external judge
(Comparator) take these statements as its trusted Challenge with an
import closure that a skeptic can read without reading Iris.

This module was carved out of `Specs/GoldenQuorumWP`, `Specs/GoldenQuorumAll`,
`Specs/GoldenQuorumThree`, `Specs/GoldenRecover` and
`Specs/AutomationTargets` by the measured statement-closure map (the same
walk the statement-TCB gate runs, grouped by module of origin): exactly the
statement-referenced `def`s that lived in Iris-reaching modules moved here,
with their docstrings; every theorem stayed where its proof lives. The
statement-TCB gate already guaranteed these definitions' *constant-level*
closures are Iris-free — this move makes the import graph say it too.

Import closure: `GoLean` core (the interpreter — the TCB), `Surface` (the
Iris-free triple/spec layer), `QuorumTargets` (the declarative quorum spec),
`GoldenQuorum`/`GoldenProgram` (the pinned lowerings). All measured clean.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenQuorum GoLean.Iris.GoldenRecover

namespace GoLean.Quorum

/-! ## The encoding predicates (from `Specs/AutomationTargets`)

They say what a heap map-snapshot has to look like to MEAN a
`MajorityConfig` / `AckedIndexer` pair. Both are stated over the entry
array the machine's `mapRangeEntries`/`mapLookup` see, at `uint64`
values — no address, no cell, no program appears in them. -/

/-- A `MajorityConfig`'s snapshot encodes the voter list `c`: the keys are
exactly `c`'s ids as `uint64` values (in some order — a map has no
order), every value is the empty struct, and the ids are in range. -/
def EncodesConfig (entries : Array (GoValue × GoValue)) (c : List Nat) : Prop :=
  (∀ p ∈ entries, ∃ v : Nat, v < 2 ^ 64 ∧ p.1 = .int (v : Int) .uint64
      ∧ p.2 = .struct ⟨"struct{}"⟩ #[] ∧ v ∈ c)
  ∧ (∀ v ∈ c, ∃ p ∈ entries, p.1 = .int (v : Int) .uint64)
  ∧ entries.size = c.length

/-- A `mapAckIndexer`'s snapshot encodes the partial map `acked`: entry
`v ↦ i` is present exactly when `acked v = some i`. A voter with no entry
is Go's "hasn't reported yet", which `ackedOrZero` reads as `0`. -/
def EncodesAcked (entries : Array (GoValue × GoValue))
    (acked : Nat → Option Nat) : Prop :=
  (∀ p ∈ entries, ∃ v i : Nat, i < 2 ^ 64 ∧ p = (.int (v : Int) .uint64,
      .int (i : Int) .uint64) ∧ acked v = some i)
  ∧ (∀ v i : Nat, acked v = some i →
      ((.int (v : Int) .uint64, .int (i : Int) .uint64) : GoValue × GoValue) ∈ entries)

/-- The heap footprint the `∀`-config statement hands the method: the
receiver `MajorityConfig` cell and its data cell, and the
`AckedIndexer`-typed argument cell holding a BOXED `mapAckIndexer`
(exactly the shape the n = 1 walk carries at `l`) with its data cell.
The two data cells' declared types are left as parameters — the walk
never reads them, so pinning them would narrow the claim for nothing. -/
def configPre (ca cba la lba : Nat) (cty lty : Option Ty)
    (ce ae : Array (GoValue × GoValue)) : Surface.HProp :=
  .sep (.pointsTo ca ⟨some (.defined ⟨"main.MajorityConfig"⟩),
                      .map ⟨some (.base ⟨cba⟩)⟩⟩)
    (.sep (.pointsTo cba ⟨cty, .mapData ce⟩)
      (.sep (.pointsTo la ⟨some (.interface ⟨"main.AckedIndexer"⟩),
                           .interface (.defined ⟨"main.mapAckIndexer"⟩)
                             (.map ⟨some (.base ⟨lba⟩)⟩)⟩)
        (.pointsTo lba ⟨lty, .mapData ae⟩)))

/-- **THE ∀-CONFIG TARGET** (`docs/2026-08-01_proof-automation-arc.md`
§THE GOAL). For every voter list `c`, every acked map `acked`, and every
heap snapshot pair encoding them, the PINNED LOWERING of the real
etcd-io/raft `main.MajorityConfig.CommittedIndex`, called on that
receiver and that `AckedIndexer`, delivers a value satisfying the
DECLARATIVE quorum spec `IsCommittedIndex` — safely (`GoSpec` = triple +
progress), in any admissible heap, with any frame intact.

This is machine-side generality matching `committedIndexRef_meets_spec`'s
math-side generality: `quorumOneKnownFuncSpec` is the single point
`c = [1]`, `acked = {1 ↦ 12}` of this surface.

Note what is NOT assumed: no *small* bound on `c.length`, so the
statement covers BOTH branches of `if len(stk) >= n` — the on-stack
`[7]uint64` reslice AND the `make([]uint64, n)` heap allocation at more
than seven voters. `c.Nodup` is the map-key uniqueness a
`MajorityConfig` has by construction. Nothing is assumed about `acked`:
a voter with no entry is Go's "has not reported yet", which
`AckedIndex` answers with `(0, false)` and `majority.go` treats as a
zero — the walk takes that iteration too.

**STATEMENT CORRECTED 2026-08-01 (phase 4) — recorded, not quietly
patched.** The original form had NO bound on `c.length` at all, and in
that form it is FALSE, not merely unproven: at `c.length ≥ 2^63` the
lowering's `n := len(c)` is a Go `int`, so `IntKind.int.normalize` wraps
it NEGATIVE; `n == 0` is then false, `len(stk) >= n` is TRUE (7 ≥ a
negative), and `srt = stk[:n]` hits `checkSliceBounds`' negative-high
arm — a panic, i.e. a configuration that `Progress` counts as stuck. The
`c.length < 2 ^ 63` hypothesis is the REPRESENTABILITY side condition
that says the config fits in the machine `int` the lowering counts it
with (the same bound `GoldenQuorumThree.wp_ci_loop` already carried as
`hsmall`); it is a property of Go's `int`, not of the target. Not
mechanized as a refutation — exhibiting the panicking run at 2^63
entries is a separate cost and is recorded as owed, exactly as the
`quorumAckedIndexFuncSpec2_statement` correction was.

**DISCHARGED 2026-08-01** (phase 4) by
`Specs/GoldenQuorumAll.committedIndexAllConfigs`, whose type IS this def
— that application is the statement-identity check, so weakening the
statement to fit the proof would break this file. No separate
"meets-spec" corollary is needed: the postcondition here IS the
declarative spec (`IsCommittedIndex`), unlike the concrete-instance
targets which pin a number and get their declarative restatement
separately. The first-order readout and the negative twin at the 3-voter
encoding are `committedIndexAllReturnsSix` / `committedIndexAllNotTwelve`
in `Specs/GoldenQuorumAll`. This def is left exactly as written apart
from the recorded representability correction above. -/
def committedIndexAllConfigs_statement : Prop :=
  ∀ (c : List Nat) (acked : Nat → Option Nat)
    (ce ae : Array (GoValue × GoValue)) (cty lty : Option Ty)
    (ca cba la lba ra : Nat) (w : GoValue),
    c.Nodup →
    c.length < 2 ^ 63 →
    EncodesConfig ce c →
    EncodesAcked ae acked →
    [ra, ca, cba, la, lba].Nodup →
    Surface.GoSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods
      [[("$callres", Loc.base ⟨ra⟩), ("c", Loc.base ⟨ca⟩),
        ("l", Loc.base ⟨la⟩)]]
      (.sep (.pointsTo ra ⟨some (.int .uint64), w⟩)
        (configPre ca cba la lba cty lty ce ae))
      (.call #[.var "$callres"] ⟨"main.MajorityConfig.CommittedIndex"⟩
        #[.var "c", .var "l"])
      (.ex fun (n : Int) =>
        .sep (.pointsTo ra ⟨some (.int .uint64), .int n .uint64⟩)
          (.ex fun (r : Nat) =>
            .pure (n = (r : Int) ∧ IsCommittedIndex c acked r)))

/-! ## The concrete instances' data (from `Specs/AutomationTargets` and
`Specs/GoldenQuorumWP`) -/

/-- The 3-voter config `{1,2,3}` and the snapshot that encodes it. -/
def threeConfigEntries : Array (GoValue × GoValue) :=
  #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[]),
    (.int 2 .uint64, .struct ⟨"struct{}"⟩ #[]),
    (.int 3 .uint64, .struct ⟨"struct{}"⟩ #[])]

/-- `mapAckIndexer{1:12, 2:5, 3:6}` — etcd's own `committedThreeAll` row
(`testdata/majority_commit.txt`), as a snapshot. -/
def threeAckedEntries : Array (GoValue × GoValue) :=
  #[(.int 1 .uint64, .int 12 .uint64),
    (.int 2 .uint64, .int 5 .uint64),
    (.int 3 .uint64, .int 6 .uint64)]

/-- The same data as a math-level partial map. -/
def ackedThreeAll : Nat → Option Nat :=
  fun v => if v = 1 then some 12 else if v = 2 then some 5
           else if v = 3 then some 6 else none

/-- The one-voter instance's acked data: voter `1` reported index `12`
(the `committedOneKnown` driver's map literal). -/
def ackedOneKnown : Nat → Option Nat := fun v => if v = 1 then some 12 else none

end GoLean.Quorum

namespace GoLean.Surface

open GoLean.GoCore GoLean.Quorum

/-! ## Headline `GoFuncSpec*` statements (from `Specs/GoldenQuorumWP`,
`Specs/GoldenRecover` and `Specs/AutomationTargets`) -/

/-- **THE ARC'S NAMED GOAL — now a THEOREM** (`quorumOneKnownFuncSpec`,
`Specs/GoldenQuorumWP`, quorum pilot phase 4 summit, 2026-07-31). The
`GoFuncSpec` form over the PINNED ACTUAL LOWERING of the real
etcd-io/raft quorum source:
"`committedOneKnown()` takes no arguments, needs no heap, and returns
12" — ∀-quantified over the caller's target cell, its prior value, and
the frame, exactly as `recoverFuncSpec_statement`/
`goldenFuncSpec_statement`. The driver builds `MajorityConfig{1:{}}` and
`mapAckIndexer{1:12}` and calls `run → CommittedIndex`, so discharging
this walks the real interface dispatch, the real map range, the real sort
extern and the real defined-type conversions.

`12` is `committedIndexRef [1] ackedOneKnown` (`committedIndexRef_oneKnown`,
`rfl`), so this discharge plus `committedIndexRef_meets_spec` (PROVEN)
yields `IsCommittedIndex` on this instance — the tier-1 claim, packaged
as `quorumOneKnownMeetsSpec`. -/
def quorumOneKnownFuncSpec_statement : Prop :=
  GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
    quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
    (fun n => .pure (n = 12))

/-- **TARGET — the negative twin, and the one thing this slice did NOT
prove.** Stated as an UNCONDITIONAL refutation.

*Provenance corrected 2026-07-31 (pre-merge audit, finding 6):* this def
and `quorumOneKnownFuncSpec_statement` were repeatedly described as
"phase-0" targets. Git says otherwise — neither exists at the phase-0
commit `9bd409c`; both were first written in phase 4 at `39891ae`, one
and two commits before their discharge. The statement-before-machinery
discipline WAS honoured (target commits precede result commits), but in
the weaker one-to-two-commit sense, not from phase 0. The genuine phase-0
targets are `committedIndexRef_meets_spec_statement` and the
`GoFuncSpec2` shape (`QuorumTargets.lean`).

It does not
follow from the positive discharge: `GoTriple` quantifies over
TERMINATING runs, so both the `= 12` and the `= 11` spec are vacuously
true of a program with no terminating run, and refuting this def requires
exhibiting one — a kernel evaluation of the interpreter over the whole
pinned program, a separate cost. The run-conditioned twin
`quorumOneKnownNotEleven` (the `goldenNotThree` shape) IS proven in
`Specs/GoldenQuorumWP`; this def stays a target and no theorem names it.
Recorded, not quietly restated. -/
def quorumOneKnownNotEleven_statement : Prop :=
  ¬ GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
      (fun n => .pure (n = 11))

/-- The concrete receiver the `AckedIndex` spec is stated on: a
`mapAckIndexer` cell at `ma` holding a map whose data cell at `mba` is
the single entry `3 ↦ 12` — the smallest instance that makes the comma-ok
answer non-trivial (a HIT, so the `found` result is `true` and the value
is the map's, not the zero default). -/
def ackedIndexerPre (ma mba : Nat) : HProp :=
  .sep (.pointsTo ma ⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                      .map ⟨some (.base ⟨mba⟩)⟩⟩)
    (.pointsTo mba ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                    .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩)

/-- **TARGET, now PROVEN in `Specs/GoldenQuorumWP`**
(`quorumAckedIndexFuncSpec2`): the
implementation method `main.mapAckIndexer.AckedIndex` of the PINNED
lowering at `GoFuncSpec2` strength — its `(Index, bool)` result pair is
the arity widening the pilot forces. Reads: *`m.AckedIndex(3)` on the
`{3 ↦ 12}` receiver, into any two caller cells (int-kind and bool, any
prior values), in any admissible heap with any frame, terminates only in
states where those cells hold `12` and `true`.*

**Statement corrected 2026-07-31 (recorded, not quietly patched).** The
FIRST form of this statement — written at `39891ae`, in phase 4, not at
phase 0 as this note previously said (provenance corrected same day,
pre-merge audit finding 6) — passed `#[]` arguments to a two-parameter
method: the arity
check in `enterFrame` fails closed, so the configuration is STUCK, so
`Progress` — and with it the whole statement — was FALSE, not merely
unproven; and its postcondition `b = true → n = 12` was satisfiable by a
method that never finds anything. Both are fixed here: the receiver and
index are real arguments (`GoFuncSpec2`'s new caller-environment
parameter is what makes a heap-carried receiver denotable at all), and
the postcondition pins BOTH results positively. -/
def quorumAckedIndexFuncSpec2_statement : Prop :=
  ∀ ma mba : Nat,
    GoFuncSpec2 quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"main.mapAckIndexer.AckedIndex"⟩ .uint64
      [("m", Loc.base ⟨ma⟩)] #[.var "m", .intLit 3 .uint64]
      (ackedIndexerPre ma mba)
      (fun n b => .pure (n = 12 ∧ b = true))

/-- **TARGET (phase 3, the first widening past n = 1)**: the pinned
lowering of etcd's own `committedThreeAll` driver — `MajorityConfig{1,2,3}`
with `mapAckIndexer{1:12, 2:5, 3:6}` — returns `6`.

Why it is the right next rung and not just a bigger number: at n = 3 the
map range has `3! = 6` iteration orders and `wp_map_iter_next_key` alone
would need every one of them walked; the whole point of
`Laws/Range.wp_map_iter_inv` is that this target costs ONE generic
iteration plus an invariant. It also makes `slices.Sort` do real work
(the n = 1 sort is a no-op) and puts `pos = n - (n/2+1)` at a nonzero
index.

`6` is `committedIndexRef [1,2,3] ackedThreeAll` (`rfl`,
`Specs/AutomationTargets.committedIndexRef_threeAll`), so this
discharge plus `committedIndexRef_meets_spec` yields `IsCommittedIndex`,
exactly as `quorumOneKnownMeetsSpec` packages the n = 1 rung.

**DISCHARGED 2026-08-01** (phase 3) by
`Specs/GoldenQuorumThree.quorumThreeAllFuncSpec`, whose type IS this def
— that application is the statement-identity check, so weakening the
statement to fit the proof would break this file. The declarative
restatement is `quorumThreeAllMeetsSpec`. This def is left exactly as
written. -/
def quorumThreeAllFuncSpec_statement : Prop :=
  GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
    quorumLowered.methods ⟨"committedThreeAll"⟩ .uint64 #[] .emp
    (fun n => .pure (n = 6))

/-- **TARGET — the 3-voter negative twin.** Stated as an UNCONDITIONAL
refutation at `12` (the largest acked index — the answer a
"returns something a voter acked" bug would give).

It does NOT follow from the positive discharge, and the reason is
recorded once for the whole family (`quorumOneKnownNotEleven_statement`
says the same): `GoTriple` quantifies over TERMINATING runs, so both the
`= 6` and the `= 12` spec are vacuously true of a program with no
terminating run. Refuting this needs a terminating run EXHIBITED — a
kernel evaluation of the interpreter over the pinned program. The
cheap, honest twin is the run-conditioned one
(`quorumOneKnownNotEleven`'s shape), which phase 3 landed beside the
positive result: `Specs/GoldenQuorumThree.quorumThreeAllNotTwelve`. This
def stays a TARGET and no theorem names it. -/
def quorumThreeAllNotTwelve_statement : Prop :=
  ¬ GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedThreeAll"⟩ .uint64 #[] .emp
      (fun n => .pure (n = 12))

/-- **The recover function spec, as a statement** (the arc's slice-B
target): "`recoverDirect()` takes no arguments, needs no heap, and
returns 7" — over the PINNED ACTUAL LOWERING, ∀-quantified over the
caller's target cell, its prior value, and the frame. -/
def recoverFuncSpec_statement : Prop :=
  GoFuncSpec recoverLowered.typeDefs.toList recoverLowered.funcs
    recoverLowered.methods ⟨"recoverDirect"⟩ .int #[] .emp
    (fun n => .pure (n = 7))

/-! ## Seeded states for the first-order readouts

Each readout theorem (`…Returns…`, rung 2 of the statement ladder) runs
`execStmt` from one of these pinned initial states and observes the result
cells with `loadLoc` — no separation logic in the statement. The seeds
live here because the readout THEOREM statements reference them. -/

/-- The initial heap the one-cell readouts run against: one cell at base 0
holding the caller's target, exactly as `GoFuncSpec` quantifies it
(quorum driver shape, `uint64`). -/
def quorumOut : Heap := [(Loc.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]

def quorumOutEnv : LocalEnv := [[("$callres", Loc.base ⟨0⟩)]]

/-- The recover pin's one-cell seed (`int`-kind target). -/
def recoverOut : Heap := [(Loc.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)]

def recoverOutEnv : LocalEnv := [[("$callres", Loc.base ⟨0⟩)]]

/-- The 3-voter driver readout's caller environment (its heap is
`quorumOut` — same one-cell `uint64` shape). -/
def threeOutEnv : LocalEnv := [[("$callres", Loc.base ⟨0⟩)]]

/-- The initial heap the two-cell readout runs against: the two caller
target cells (0: `Index`-kind int, 1: bool), the receiver box at 2, and
the `{3 ↦ 12}` map data at 3 — exactly `quorumAckedIndexPre_satisfiable`'s
witness shape, as a machine heap. -/
def ackedIndexOut : Heap :=
  [(Loc.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩),
   (Loc.base ⟨1⟩, ⟨some .bool, .bool false⟩),
   (Loc.base ⟨2⟩, ⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                   .map ⟨some (.base ⟨3⟩)⟩⟩),
   (Loc.base ⟨3⟩, ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                   .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩)]

/-- The caller environment: the two result targets plus the receiver
binding `m`, exactly as `GoFuncSpec2`'s caller scope quantifies them. -/
def ackedIndexOutEnv : LocalEnv :=
  [[("$callres0", Loc.base ⟨0⟩), ("$callres1", Loc.base ⟨1⟩),
    ("m", Loc.base ⟨2⟩)]]

/-- The seeded heap the ∀-config readout runs against: the caller's result
cell at `0`, the `MajorityConfig{1,2,3}` receiver at `1`/`2`, and the
`mapAckIndexer{1:12, 2:5, 3:6}` argument, boxed at the `AckedIndexer`
interface, at `3`/`4`. -/
def allOut : Heap :=
  [(Loc.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩),
   (Loc.base ⟨1⟩, ⟨some (.defined ⟨"main.MajorityConfig"⟩),
                   .map ⟨some (.base ⟨2⟩)⟩⟩),
   (Loc.base ⟨2⟩, ⟨none, .mapData threeConfigEntries⟩),
   (Loc.base ⟨3⟩, ⟨some (.interface ⟨"main.AckedIndexer"⟩),
                   .interface (.defined ⟨"main.mapAckIndexer"⟩)
                     (.map ⟨some (.base ⟨4⟩)⟩)⟩),
   (Loc.base ⟨4⟩, ⟨none, .mapData threeAckedEntries⟩)]

def allOutEnv : LocalEnv :=
  [[("$callres", Loc.base ⟨0⟩), ("c", Loc.base ⟨1⟩), ("l", Loc.base ⟨3⟩)]]

end GoLean.Surface
