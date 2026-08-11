import GoLeanProofs.ZzGateFixtureSupport
import GoLeanProofs.Specs.GoldenTargets

/-!
# Completion-pin gate: the ESCAPE-SHAPE fixtures (S1 audit round 2)

Negative-test fixtures for the REBUILT (semantic) completion-pin gate
in `Audit.lean` — one tracked instance of each escape shape the round-2
delta review proved against the first gate, each of which the rebuilt
gate must FLAG (its negative tests assert so by constant name) while
enforcement excludes exactly this module and the warning fixture:

- `fixtureSpecCUnpinned` — a `GoSpecC`-typed export: the first gate's
  one-level type scan never saw `GoTripleC` through the `GoSpecC`
  definition (the review's MAJOR). The rebuilt gate's deep
  `defnInfo`-unfolding closure walk classifies it.
- `fixtureDefTriple` — a `def`-exported triple: the first gate's
  `theorem`-only filter dropped it.
- `fixtureWrappedTriple` — a theorem stated at a definitional wrapper
  type: classified by the deep walk, but its stated type carries NO
  extractable `GoTripleC`/`GoSpecC` application — the gate FAILS
  CLOSED on such exports (state the triple directly), and this
  fixture pins that arm.
- The MODULE's own name (`Specs.Zz…`, outside the first gate's
  `Specs.Chan*` glob) is the out-of-glob scope fixture: the rebuilt
  gate's scope is ALL of `GoLeanProofs.Specs.*`.

The fixtures are HONEST theorems (no `sorry` — the axiom sweep forbids
it; the delta review's own `.tmp` probe used `sorry` for the
`ProgressExecC` half, which cannot be committed): each is a triple
over the unsatisfiable precondition `.pure False`, provable outright —
and thereby also a permanent reminder that a `GoTripleC`/`GoSpecC`
with an unsatisfiable pre is vacuously true, exactly the class the
non-vacuity doctrine's witnesses exist to exclude. `zzFixtureProg` is
a fixture-private program constant, so no completion pin for it exists
anywhere (the pairing is per-PROGRAM) and the fixtures stay flagged
forever.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-- Fixture-private program: nothing else states anything about it. -/
def zzFixtureProg : Stmt := .seqn #[]

/-- ESCAPE SHAPE 1 — `GoSpecC`-typed, no completion pin (vacuous over
the unsatisfiable pre; module docstring). -/
theorem fixtureSpecCUnpinned :
    GoSpecC [] #[] #[] [] (.pure False) zzFixtureProg .emp :=
  ⟨fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim,
   fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim⟩

/-- ESCAPE SHAPE 2 — a `def`-exported triple type. -/
def fixtureDefTriple :
    GoTripleC [] #[] #[] [] (.pure False) zzFixtureProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- The definitional wrapper for escape shape 3. -/
def ZzWrappedTriple : Prop :=
  GoTripleC [] #[] #[] [] (.pure False) zzFixtureProg .emp

/-- ESCAPE SHAPE 3 — a theorem stated at the wrapper type: the deep
walk classifies it, and the gate fails closed on the missing
extractable application (this fixture pins that arm). -/
theorem fixtureWrappedTriple : ZzWrappedTriple :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-! ## Round-3 escape shapes (S1 audit round 3 — the verifier's probe
shapes P2/P3/P4/P4b/P12, kept forever: the gate that has fallen three
times keeps every attacker's shape as a tracked fixture) -/

/-- P2 — the STRUCTURE-WRAPPER escape: the wrapper `Prop` structure
lives OUTSIDE `Specs.*` (`ZzGateFixtureSupport`), so only the walk's
`.inductInfo → ctors` arm can see the triple through it. This is the
shape the round-3 CRITICAL proved invisible to the `| _ => pure ()`
wildcard walk. Expected gate class: WRAPPER-HIDDEN. -/
theorem fixtureStructWrapped : ZzStructWrappedTriple :=
  ⟨fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim⟩

/-- P3 — the OPEN-TERM escape: the triple's `prog` is a bound variable
of the theorem's own telescope; the extracted argument is a loose
de Bruijn index, which round 2's structural pairing could collide
with a generic pin lemma's binder. Expected gate class: OPEN-TERM
(fail closed — a ∀-program triple has no per-program pin; a GENUINE
generic lemma of this shape belongs on the gate's exact-name
allowlist with a reason, never silently). -/
theorem fixtureOpenProgTriple {prog : Stmt} (_h : True) :
    GoTripleC [] #[] #[] [] (.pure False) prog .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- Fixture-private program for the self-pin shape. -/
def zzSelfPinProg : Stmt := .seqn #[.seqn #[], .seqn #[], .seqn #[]]

/-- P4 — the SELF-PIN escape: the theorem carries its OWN unproved
`TerminatesNormallyC` as a HYPOTHESIS; round 2's
mention-counting pass would have counted it as a pin. A pin is a
CONCLUSION, never a hypothesis. Expected gate class: UNPAIRED. -/
theorem fixtureSelfPin
    (_h : TerminatesNormallyC [] {} zzSelfPinProg) :
    GoTripleC [] #[] #[] [] (.pure False) zzSelfPinProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- Fixture-private program for the decoy shape. -/
def zzDecoyProg : Stmt := .seqn #[.seqn #[.seqn #[]]]

/-- P4b (decoy half) — a theorem that MENTIONS `TerminatesNormallyC`
for the decoy program without ASSERTING it (the conclusion's head is
`Or`, discharged right). Must NOT count as a pin. -/
theorem fixtureDecoyPin :
    TerminatesNormallyC [] {} zzDecoyProg ∨ True :=
  Or.inr trivial

/-- P4b (triple half) — the unpinned triple the decoy would have
"paired" under round 2's mention-counting. Expected gate class:
UNPAIRED (the decoy does not save it). -/
theorem fixtureDecoyTriple :
    GoTripleC [] #[] #[] [] (.pure False) zzDecoyProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- Fixture-private program for the namespace-child shape. -/
def zzChildProg : Stmt := .seqn #[.seqn #[.seqn #[.seqn #[]]]]

/-- P12 — the NAMESPACE-CHILD escape: a user-declared theorem inside a
fixture root's namespace. Round 2's PREFIX-based fixture exclusion
silently swallowed it; the round-3 exclusion is exact-name plus a
generated-suffix whitelist, so this fixture is flagged by the raw
checker and excluded only because it is LISTED by its exact name.
Expected gate class: UNPAIRED. -/
theorem fixtureDefTriple.namespaceChildProbe :
    GoTripleC [] #[] #[] [] (.pure False) zzChildProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-! ## Round-4 escape shapes (S1 gate-verification generation 4 —
the standing rule: every attacker shape becomes a tracked fixture) -/

/-- Fixture-private program for the opaque-export shape. -/
def zzOpaqueProg : Stmt := .seqn #[.block #[] #[]]

/-- R4-1a — the OPAQUE EXPORT: round 3 removed the walk's wildcard but
left one in the classification KIND filter (`| _ => false`), so an
`opaque` triple was never classified — the round-3 critical's exact
signature, one level up. Expected gate class: UNPAIRED. -/
opaque fixtureOpaqueTriple :
    GoTripleC [] #[] #[] [] (.pure False) zzOpaqueProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- R4-1b (mutation trigger for the `.opaqueInfo → value` EDGE arm,
which no round-3 fixture exercised): an opaque `Prop` whose VALUE is
the triple — reachable only through that arm. -/
opaque ZzOpaqueWrappedProp : Prop :=
  GoTripleC [] #[] #[] [] (.pure False) zzOpaqueProg .emp

/-- R4-1b (the classified consumer): its type mentions the opaque
`Prop`, so it is classified iff the opaque-VALUE edge arm is alive.
Expected gate class: WRAPPER-HIDDEN. -/
theorem fixtureOpaqueEdge : ZzOpaqueWrappedProp → True := fun _ => trivial

/-- Fixture-private program for the guarded-pin shape. -/
def zzGuardedProg : Stmt := .seqn #[.block #[] #[], .seqn #[]]

/-- R4-2a — the HYPOTHESIS-GUARDED PIN: an assertion under an
undischarged premise is not an assertion (round 3's
mention-is-not-assertion, one level up: `gateConclusion` peeled
hypothesis binders too). Pins must be BINDER-FREE; this one must
never count. -/
theorem fixtureFalseGuardedPin (h : False) :
    TerminatesNormallyC [] {} zzGuardedProg :=
  h.elim

/-- R4-2b — the export the guarded pin would have "paired". Expected
gate class: UNPAIRED (the guarded pin does not save it). -/
theorem fixtureGuardedTriple :
    GoTripleC [] #[] #[] [] (.pure False) zzGuardedProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- Fixture-private program for the suffix-abuse shape. -/
def zzSuffixProg : Stmt := .seqn #[.seqn #[.block #[] #[]]]

/-- R4-3 — the GENERATED-SUFFIX ABUSE: a real export named as a
pseudo-generated child (`eq_*`) of a listed fixture root; round 3's
suffix whitelist silently excluded it. Exclusion under fixture roots
is now by EXACT LIST ONLY, so this fixture is flagged and excluded
only because it is listed by its exact name. Expected gate class:
UNPAIRED. -/
theorem fixtureDefTriple.eq_realExport :
    GoTripleC [] #[] #[] [] (.pure False) zzSuffixProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- Fixture-private program for the underscore shape. -/
def zzUnderscoreProg : Stmt := .seqn #[.seqn #[], .block #[] #[]]

/-- R4-4 — the LEADING-UNDERSCORE NAME: `Name.isInternal` treats it as
compiler-internal, but it is user-writable; round 3's blanket
`isInternal` skip dropped it from both passes. The skip is now
`_private`-root only. Expected gate class: UNPAIRED. -/
theorem _fixtureUnderscoreTriple :
    GoTripleC [] #[] #[] [] (.pure False) zzUnderscoreProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- R4-5 — the ENVIRONMENT-MISMATCH export: `goldenDriver` HAS a
completion pin (`goldenTerminatesNormallyC`, under `outEnv`), but this
export states a triple for the same program under a DIFFERENT `env₀`
(`[]`) — round 3's prog-only pairing key would have paired them. The
key is now `(env₀, prog)`. Expected gate class: UNPAIRED. (The
remaining, deliberately UNCHECKED axis is the pin-seed-vs-export-pre
relation — the gate enforces anchor existence per `(env₀, prog)`,
never precondition satisfaction; that stays the witness discipline's
job, recorded at the gate.) -/
theorem fixtureEnvMismatchTriple :
    GoTripleC [] #[] #[] [] (.pure False) goldenDriver .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

end GoLean.Surface
