import GoLean.GoCore.Multi

/-!
# The slow enumeration semantics — the membership lane's statement spec

THE BINDING DESIGN CONSTRAINT (Mike, 2026-08-20; design note
`docs/2026-08-21_w32-por-design.md` §0): top-level enumeration claims
are stated over the *slow but obviously correct* execution semantics.
This file IS that semantics: the machine's reachable observation set,
defined as the ∃-image of the unmodified interpreter driver
(`execProgLoop`) over every choice stream and every fuel. Nothing here
is enumeration machinery — `Obs` is the observation vocabulary,
`obsOf?` a five-arm projection, `SlowObs` the ∃-form. Any optimized
enumerator (the dedup engine, `GoLean/EnumDedup.lean`) licenses
conclusions only through a theorem into THIS definition
(`checkCert_slowObs`, `EnumDedupSound.lean`); no statement mentions
the optimized machinery.

A certified membership/confluent row's claim, restated over this spec
(same substance as the CLI lane's "distinct observations over the
whole choice tree"; the ∃-fuel form makes "terminating members"
literal — a divergent branch observes nothing at any fuel):

    ∀ o, o ∈ S ↔ SlowObs resultLocs m₀ r₀ o
-/

namespace GoLean.GoCore.Machine

/-- One observation of a pool run — the membership lane's member
vocabulary (`enumPoolRun`'s statuses, as data): main's normal terminal
with the readout values, or a Go TERMINAL the run stopped on (`Terminal`,
Value.lean: an unrecovered panic in any goroutine, a `fatal` throw,
deadlock, the race detector's refusal). Fuel exhaustion and the
refusals (stuck/unsupported/internal) are NOT observations (`obsOf?` is
`none`; the checker fails loud on them). Since wave (iii) B2 the
vocabulary is the outcome grammar's own `Terminal`, so EVERY Go
terminal is statable — the former capability bound (`Obs` had no
`fatal`/`deadlock` constructor: Q8 of the W3.2 Q-rows, audit-2 N-3,
launch audit W-1/D3-F-1) is closed at the TYPE. The ENGINE and the
CHECKER still refuse `fatal` and `deadlock` members loudly
(`EnumDedup.nodeObs`, `checkEdge`/`checkNode`: no membership handling
for them yet — a certified set never contains one silently); admitting
them is a lane decision, not a type change. -/
inductive Obs where
  | ok (values : List GoValue)
  | terminal (t : Terminal)
  deriving Repr

/-- Project a driver result to its observation, if any. The `.ok`
readout mirrors `enumPoolRun`'s terminal (`loadMany` at the pinned
result locations); an errored readout is no observation (the checker
refuses such nodes — fail closed, never a silent member); every Go
terminal IS one. -/
def obsOf? (resultLocs : List Loc) :
    Except Stop (ExecState × Choices) → Option Obs
  | .ok (σf, _) =>
      match loadMany σf resultLocs with
      | .ok vs => some (.ok vs)
      | .error _ => none
  | .error (.terminal t) => some (.terminal t)
  | .error _ => none

/-- **THE SLOW SEMANTICS** (design note §1): observation `o` is
reachable from the seeded pool `(m₀, r₀)` — some choice stream, some
fuel, the unmodified driver. This is the top-level claims' entire
vocabulary for enumeration results. -/
def SlowObs (resultLocs : List Loc) (m₀ : MultiConfig) (r₀ : RaceState)
    (o : Obs) : Prop :=
  ∃ fuel ch, obsOf? resultLocs (execProgLoop fuel m₀ r₀ ch) = some o

end GoLean.GoCore.Machine
