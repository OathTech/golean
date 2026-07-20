# The end-state theorem: Iris dissolves (2026-07-20)

Question (design review): what is the final theorem we ship, and can it be
believed **without understanding any Iris**? Answer: yes — that is the standard
Iris *adequacy* architecture, and it is our designed end state. This note pins
the shape so every layer aims at it.

## The shape

Iris appears only in **proof terms**, never in **statements**. The pipeline:

```
Iris WP proof  ──go_adequacy──▶  plain operational theorem over Rel.Step
   (baroque, trusted-by-kernel)      (readable, Iris-free)
```

`adequate` is defined purely over `Step`/`Config`/`ExecState` — inductive
relations over plain data. No `iProp`, no cameras, no ghost state, no `∗`. The
WP machinery is *how we prove it*; the kernel checks the proof term; `#print
axioms` shows only `[propext, Classical.choice, Quot.sound]`. Iris has exactly
the status of a heavy tactic library: methodology, not meaning.

**Slice end-state theorem (the L6 target, stated Iris-free):**

```
theorem incViaCall_returns_two (σ : ExecState) (h : WellFormedInit σ prog) :
    ∀ c' σ', Steps (initConfig prog) σ c' σ' → Config.terminal c' →
      resultOf c' σ' = .int 2
-- plus no-stuck: every reachable non-terminal config can step
```

To audit this you read: `Rel.lean` (~370 lines of inductive rules),
`Syntax/Value/State` (data), and the program term. Nothing else.

**Raft end-state theorem (the north star, same shape):** an invariant over
`Step`-reachable states of the N-node model — "no two leaders in the same
term" / quorum-intersection safety — again a plain statement over the
operational semantics. (Its state space/message model is TODO F5.)

## What makes it "about the differentially tested semantics"

Two artifacts today: `Eval` (executable, differentially validated against
`go run`) and `Rel.Step` (proven-about). Punch-list **item 6** (correspondence)
is what fuses them: `execStmt … = .ok r → Steps … r`. After it, the end theorem
transfers to the *executable* semantics — statable as "for all fuel, if the
interpreter returns, it returns 2," about a function you can literally run —
and the differential corpus is evidence that *that same function* is real Go.
The trusted base of the final property is then:

1. Lean's kernel + the classical trio (machine-checked);
2. `Rel.lean`+`Eval.lean` correctly model Go — **pinned by the differential
   corpus against `go run`** (our differentiator vs Goose's trusted translator);
3. the frontend emitted the real program — same differential evidence (the
   tested IR *is* the proven IR).

No Iris anywhere in that list.

## What blocks full dissolution today (all already on the punch list)

- **Hypotheses leaking into witnesses** — `wp_assign_lit` still carries the
  `hstore` side-condition; a truly dissolved theorem has *zero* hypotheses
  beyond well-formedness. Item 1 closes it; item 2 (the closed `adequate`
  end-to-end witness) is precisely the *first demonstration* of dissolution.
- **Adequacy's panic scope** — `go_adequacy` covers non-panicking runs (#24);
  fine for "returns 2", must be widened (panics-as-values) before "never
  crashes" claims.
- **The correspondence wall** (item 6) — until proven, the dissolved theorem is
  about `Rel.Step` only, and its link to the differentially tested interpreter
  is informal.

## Design rule this pins

**No Iris in statements.** Every user-facing/end-state theorem must be stated
over `Rel.Step`/`Eval` and plain data. If a spec needs `iProp` to *state*, it is
an internal lemma, not a deliverable. (Mid-execution/concurrency reasoning may
use Iris internally — invariants, ghost state — but the exported claim is always
an operational statement, e.g. an invariant over reachable states.) This keeps
the believability audit to: kernel + axioms + ~400 lines of semantics + the
differential evidence.
