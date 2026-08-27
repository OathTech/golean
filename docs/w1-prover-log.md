# W1 log (2026-08-27) — one writer: the w1-prover worker

**QUANTIFIER-AUDIT LINE (the charter's opening requirement):** W1
builds the RULES that later discharge ∀-states (the spec former: the
`Spec` judgment ∀-quantified over a precondition predicate), composes
∀ch (threading the demonic tape through the judgment and its
composition rules), and bridges ∃n specs to the ∀-fuel/∃-fuel
sentences (the glue family: `runProgramM_mono`,
`runProgramM_readout_of_total`, `runConfig_prefix_classify` + the
two-phase lift). W1 itself proves no end-theorem quantifier — it is
the machinery wave, and says so. Every theorem in this unit is either
a RULE (consumed by W2–W5 to discharge quantifiers) or a PILOT
INSTANCE measuring the rules' cost (Leg A/B/C), labeled as such.

Governing docs: `docs/2026-08-27_clean-proof-plan.md` §W1 (as
professor-amended), `docs/2026-08-27_proof-structure-explained.md` §1,
`CLAUDE.md` (charter), `docs/operational-lessons.md` (build
discipline). Branch `w1-prover` @ 84b5edb3 off post-reset main.
Conventions: capped builds only, box-wide lock for full builds
(taken 04:57Z, owner file updated), zero sorry/native_decide/new
axioms, design note + LINEAGE before code, [AGENT] provenance on
judgment calls, derivation-anchored numbers.

## Judgment calls and checkpoints

- [AGENT] Build lock: owner file at the primary checkout read
  RELEASED (w0-reset's exit); zero batch lake/lean builds on the box
  (only idle LSP workers from a prior arc4d session + an unrelated
  project's server). Took the lock for the w1 cold build + gates.
- [AGENT] PROBE-FIRST on the summit (frame/footprint + the
  continuation-parametric lift), per the charter's starred-summit
  rule. The decisive question found while reading the landed engine:
  window facts (`symEvalWindow*_refines`) are proved at CLOSED
  configs — the arc4d becomeFollower span is anchored at
  `k = .stop`, `env = []` — but the plan's judgment is
  CONTINUATION-PARAMETRIC (∀ env k), which is what makes the call
  rule compose. Two candidate routes, both classics:
  (a) a plug/bind rule (wp_bind / evaluation-context locality):
      a full `stepFn` arm walk (~110 arms, StepSim-scale) proving
      tail-replacement commutation below a barrier frame;
  (b) OPEN-TAIL WINDOW EVALUATION: evaluate the window on a config
      whose below-frame tail is an open variable `k` (and open
      caller `env` in the frame's tenv slot) — kernel reduction
      never inspects below the barrier on a successful span, so
      `rfl` closes the window fact ∀ k for free (wp_bind realized
      by computational reflection instead of by a walk).
  Probe result (artifacts/w1/ProbeOpenTail.lean): route (b) WORKS —
  see the probe record below. Route (a) is recorded as the promoted
  escape if open-term reduction fails at scale (the escape ladder's
  first rung for this obligation).

## Probe record

- ProbeOpenTail (3 examples: span-exit shape at open `k`; open
  caller `env` in the frame's tenv; a 5-step seq+unwind span under
  the barrier with the open tail below): `rfl` closes ALL THREE
  (artifacts/w1/ProbeOpenTail.lean, exit 0, run against the cold
  build; the probe examples are folded into the judgment module as
  tracked non-vacuity examples so the finding is build-enforced).
  Route (b) is the driver's route. Cost of route (a) if ever needed
  at scale: the analogous landed arm walk `Frame/StepSim.lean` is
  795 lines (measured, `wc -l`).
- Cold build of the fresh worktree: GREEN, 508 jobs
  (artifacts/w1/cold-build.log, EXIT=0; capped 96G, threads 8,
  box lock held).
- [AGENT] FRAME-DESIGN DEAD ENDS, measured by hand-derivation
  before any build (recorded because they shape §3 of the design
  note): (i) identity-placement FrameSim is impossible with a
  nonempty frame (`fr_avoid` quantifies over ALL of ρ's image =
  every base address); (ii) aligned-prefix canonical layouts still
  cannot cover a caller's env/k — those live at frame-region
  addresses, which are OUTSIDE ρ's image by construction (that gap
  is exactly where `fr` cells sit); (iii) `bodies_inv` forces every
  transport-admissible ρ to fix the 31 twin global addresses, so
  the arc4d fixture (raft cell at address 0) is canonical-only —
  transported use needs a re-laid fixture. Conclusion folded into
  the design note: the footprint frame = FrameSim (state half) +
  plug rule (control half); canonical specs dodge plug via open-tail
  windows; framed CONSUMPTION at a foreign call site does not.
