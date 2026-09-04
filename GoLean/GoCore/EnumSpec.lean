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
`obsOf?` a six-arm projection, `SlowObs` the ∃-form. Any optimized
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
with the readout values, an unrecovered panic (any goroutine), or the
race detector's refusal. Deadlock, fuel exhaustion, stuck/unsupported/
internal errors, AND `Stop.fatal` are NOT observations (the lane
fails loud on them; `obsOf?` is `none`). The fatal exclusion is a
CAPABILITY bound, not just a refusal: `Obs` has no fatal constructor,
so an envelope containing a fatal member (a `go` of a nil func,
sync-misuse fatals — modeled machine behaviors) is structurally
un-statable in this vocabulary. Both lanes refuse fatal loudly, so no
accepted certificate or DFS record can silently omit a fatal member;
the widening (`Obs.fatal`, Q8 of the W3.2 Q-rows) is graded
post-launch. (Sentence owed since audit-2 N-3; landed 2026-08-22,
launch audit W-1/D3-F-1.) -/
inductive Obs where
  | ok (values : List GoValue)
  | panic (msg : String)
  | race
  deriving Repr

/-- Project a driver result to its observation, if any. The `.ok`
readout mirrors `enumPoolRun`'s terminal (`loadMany` at the pinned
result locations); an errored readout is no observation (the checker
refuses such nodes — fail closed, never a silent member). -/
def obsOf? (resultLocs : List Loc) :
    Except Stop (ExecOutcome × Choices) → Option Obs
  | .ok (.normal σf, _) =>
      match loadMany σf resultLocs with
      | .ok vs => some (.ok vs)
      | .error _ => none
  | .ok (_, _) => none
  | .error (.panic msg) => some (.panic msg)
  | .error .raceDetected => some .race
  | .error _ => none

/-- **THE SLOW SEMANTICS** (design note §1): observation `o` is
reachable from the seeded pool `(m₀, r₀)` — some choice stream, some
fuel, the unmodified driver. This is the top-level claims' entire
vocabulary for enumeration results. -/
def SlowObs (resultLocs : List Loc) (m₀ : MultiConfig) (r₀ : RaceState)
    (o : Obs) : Prop :=
  ∃ fuel ch, obsOf? resultLocs (execProgLoop fuel m₀ r₀ ch) = some o

end GoLean.GoCore.Machine
