# The widening loop — the per-feature build-out recipe

Date: 2026-07-21. Distilled with the user from the slice + Arc B/C
experience; Arc E onward executes this loop once per ladder rung. Authority
for WHICH rung comes next: the widening ladder
(`docs/2026-07-19_vertical-slice-plan.md` §Widening), ordered by the raft
target — never by failure-order convenience.

## The loop

**(0) Intended proofs first.** For the feature category, write the target
theorems we expect to hold *with respect to the operational semantics* —
positive (the specs this feature must support, ultimately raft-shaped) AND
negative (statements that must remain refutable; see below). These are
`def : Prop`s or statement skeletons at first — the guardrail the rest of
the loop discharges. This is how the slice actually ran:
`slice_adequate`/`wp_main_returns_two` were written as targets and the
punch list was derived backwards.

**(1) Differential decomposition.** Break the target down into authored
corpus cases — isolated per-feature + edge enumeration + negative-compile
cases — BEFORE building anything (guardrails-first, CLAUDE.md). The red
frontier is then read off the baseline.

**(2) Frontend + interpreter to green.** The differential tests the whole
executable path (`go source → frontend → interpreter` vs `go run`); many
reds are lowering bugs (cf. BUG-001), not semantics bugs. Both fix under
the same oracle. Behavior claims validated by zero baseline drift.

**(3) Relation rules.** The over-approximating spec (semantic commit,
heavyweight audit class). Nondeterminism as existentials; panics as rules;
stuckness as absence.

**(4) Correspondence + laws + witnesses.**
  (4a) T1/T2 (+ T1p/T2p) case extensions — this is where (3) gets AUDITED
       against (2): empirically, ALL five semantic divergences to date were
       found by correspondence proof attempts, none by the corpus. Expect
       the back-edge (4a)→(3) — and occasionally →(2) — to fire.
  (4b) WP laws with non-vacuity witnesses in the same commit.
  (4c) Spec/adequacy over a real (eventually golden-lowered) program.

**(5) Discharge the intended proofs from (0).** Positive targets proven;
negative targets refuted (see below). Only then does the feature "count."

## Negative proof instances (step 0's second half)

The proof-layer twin of the negative compile corpus. Purpose: catch
**spec-layer trivialization** — the failure mode where the state
interpretation, a law, or the relation becomes weak enough that WRONG specs
become provable, while every existing gate stays green (the axiom sweep
catches logical unsoundness; the non-vacuity gate catches unusable laws;
neither catches this).

Form: **provable negations**, checked by the ordinary build (not
"expected-elaboration-failure" tests, which are fragile):

- **Stuckness pins**: `¬ ∃ c' σ', Step (bad-config) σ c' σ'` for configs
  that must be stuck (unbound variables, unmodeled features) — the
  relation's fail-closed behavior as theorems.
- **Wrong-spec refutations**: the evil twin of each headline spec — e.g.
  once `slice_interp_computes_two` lands, also prove no run yields `r = 3`
  (from correspondence + determinism). If the machinery ever weakens, the
  refutation breaks the build before a wrong positive can be proven.
- **Mutation-style premise pins**: for each law side-condition, an instance
  showing the condition-dropped variant false — recording WHY the premise
  exists (the vacuity bugs' mirror image).

Home: a `NegativeSpecs` module in the proofs package, referenced from
`Audit.lean` like the witnesses. First instances to write: an
unbound-variable stuckness pin; the `r ≠ 3` slice refutation (Arc D, after
the 2b readout); a `divByZero`-premise pin.
