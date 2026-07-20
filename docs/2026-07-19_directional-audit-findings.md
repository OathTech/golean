# Directional audit — findings & dispositions (2026-07-19)

A balanced adversarial directional audit (4 decorrelated reviewers on primary
sources → per-finding refute-default verification → synthesis; encoded as a
Workflow). Goal: are we on track for the north star (machine-checked etcd-io/raft
quorum safety), and do the artifacts mean what we claim? **Verdict:
on-track-with-corrections.** Findings below are the *verified* survivors (thin /
mischaracterized ones were refuted — see the last section). Every claim was
re-checked against source this session before being recorded here.

## What the audit confirms is solid (don't undersell)

- Core + proofs build green; `gocore-eval-tests` 40/40; the 8 proof-facing
  theorems axiom-clean `[propext, Classical.choice, Quot.sound]`.
- The WP laws and the correspondence target the **same single `Rel.Step`** — the
  relation-vs-relation silent-divergence risk genuinely does not exist.
- `wp_seqn`, `wp_assign`/`wp_assign_lit` are genuinely non-vacuous with discharge
  witnesses. The CEK reshape really did fix the earlier `wp_assign` hred vacuity.
- Ops is now fully total (0 `partial`); the correspondence blocker is narrowed to
  Eval's big-step cluster alone.
- Honesty/tracking discipline is a real strength: severed correspondence,
  panic-excluding adequacy, nonexistent target theorem, partial quorum coverage
  are all disclosed in dated docs / module headers — disclosed debt, not drift.
  (And `go_adequacy`'s NotStuck-excludes-panic shape is arguably the *desirable*
  one for a no-crash safety property.)

## Confirmed findings

### F1 — Struct-field / array-element WRITES are stuck (HIDDEN, major)
`b.n = 7`, `a[1] = …`, `p.n = …` fail closed at `lean-observation` ("expected
address value, got struct"). Root cause: `tools/nativefrontend/emit.go`
`fieldBase` (~736-738) and `emitAddressOf`'s SelectorExpr case (~814-815) lower
the base via a value-read (`.var`) where the **address** path needs an address
base (`.ref`/`.fieldAddr`); `GoCore.valueAsLoc` correctly rejects the struct
value and fails closed. Verified: `structs/copy-value`, `structs/pointer-field`,
`arrays/arrays` all FAIL `lean-observation` in the pinned baseline. **Why it
matters:** field/index write is the most common Go mutation and pervasive in
raft's tracker/Progress structs — it's on the north-star path. **Why hidden:**
buried among the 80 `lean-observation` fails, not in `TODO.md`, and
`docs/native-frontend-goal.md` lists "field/index access" as working (true for
reads, false for writes). GoCore already has the right primitives — this is a
frontend lowering bug. Tracked now in `TODO.md`.

### F2 — `wp_deref_store` re-shipped the vacuity pattern (major) — FIXED
Its `hres` was `∀σ₁` and unsatisfiable for the real `*p` (pointer variable:
address = value of p's cell, not a fixed-env fact), yet the docstring claimed it
was dischargeable for a concrete `*p = e` "exactly as `wp_assign`." Theorem TRUE
and non-vacuous, but only for **heap-independent** addresses (`.ref`/`&x`), and
it was dead weight (referenced nowhere). **Disposition: fixed this session** —
honest docstring scoping + `wp_deref_store_ref` discharge witness (proves
non-vacuity) + `exprR_ref_det`. The read-through `*p` case needs cell-conditioned
premises + multi-`↦` ownership (the tracked L5 increment).
**Process fix:** non-vacuity gate added to `CLAUDE.md` — every user-facing WP law
ships with a discharge witness in the same commit.

### F3 — Trust chain does not compose end-to-end (major, TRACKED)
The differential validates the `partial` Eval interpreter; the WP laws + adequacy
are proved over `Rel.Step`. The only bridge (`interpreterSound/PanicStatement`)
is a `def : Prop`, proven nowhere, imported by no proof file. So today the
interpreter and the Iris proofs are two **formally disconnected islands** — a
reader could wrongly infer "go_adequacy axiom-clean ⇒ raft safety proved."
Mitigated (honestly tracked, same Ops substrate, same Step). **The single
highest-leverage structural unlock is totalizing Eval's big-step cluster** — it
converts the correspondence Props into theorems and joins the islands. Ops being
total already narrows the gap. (Correspondence.lean header un-staled this session.)

### F4 — Concurrency justification may target the wrong concurrency (major, STRATEGIC)
"env-in-control is the concurrency prerequisite" (Rel.lean, TODO, cek-reshape-plan)
targets **goroutine / shared-heap** concurrency (raft's `node.go` goroutines,
roadmap stage 6, deferred). But raft's **safety** property is a **multi-node
distributed** property (N nodes, message passing) — which may need an
N-node-interleaving / message-soup model, not shared-heap concurrent separation
logic at all. The two are conflated. **Action: a design note deciding which
concurrency model quorum safety actually needs, BEFORE building Iris/HeapLang
fork machinery.** Not blocking today (still sequential), but write it before the
concurrency work starts. Tracked in `TODO.md`.

### F5 — The north-star target theorem has zero design content (major, TRACKED)
The top of the chain (GoCore ⇒ abstract-raft refinement + the quorum/safety
invariant) is honestly labeled "nonexistent." Risk: mistaking foundational
plumbing progress for progress toward the actual theorem. **Action: draft a
skeletal target — state space, message/failure model, invariant statement — so
depth-building has an explicit target to aim at.** Tracked in `TODO.md`.

## Course corrections (recommended sequencing)

1. **De-hide + doc-fix F1 now** (done: tracked in TODO; fix `native-frontend-goal.md`
   overclaim); fix the emit.go lowering when structs enter the proof frontier.
2. **F2 fixed; non-vacuity gate codified** (done).
3. **Prioritize Eval big-step totalization (F3)** over more WP lemmas — it joins
   the islands and is the honest "structure connects" claim. Highest leverage.
4. **Write the concurrency design note (F4)** before any fork machinery.
5. **Draft the skeletal target theorem (F5)** so the widening ladder has a target.

## Refuted / downgraded (kept for honesty)

- REFUTED: "D4-9 sequencing never decided" (the vertical-slice plan *is* that
  decision); "widening ladder goes silent after C" (stages B/C/final all get
  one-line treatment alike, final target named); "quorum 100%-pass overstates
  readiness" (no 100% claim exists; caveat sits beside the number).
- DOWNGRADED: F2 from "critical/unsound" → true-but-dead-weight + misleading
  docstring. A reviewer **hallucinated** a `proofs/ScratchVacuity.lean` as
  evidence; verification caught that it does not exist — the refute-default
  verification layer worked.
- REAL-BUT-MANAGED (not hidden): value-returning frames unmodeled, no shipped law
  proves `inc` yet, adequacy excludes panics, raft-relevant categories
  frontend-blocked — all disclosed in dated docs / headers and scheduled.
