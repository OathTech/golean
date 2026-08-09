# Verdi compatibility layer — feasibility study + spike (2026-08-09)

**Status:** exploratory; worktree `verdi-compat` (branch `worktree-verdi-compat`
off `main` @ `3d215822`), deliberately isolated from the main-line build.
Nothing here touches `lakefile.toml`, `GoLean/`, `proofs/`, or the baseline.

**The question (user prompt):** Verdi has a Rocq proof of Raft. Can we build a
compatibility layer that ingests *their* spec into Lean, so we can prove the
real Go (etcd-io/raft) against a spec already known to satisfy Raft's safety
properties — i.e. know our Raft spec is *the same as theirs*?

**Answer in one line:** yes, and more cheaply than expected — Verdi's Raft spec
is ~900 lines of plain first-order functional Rocq that ports 1:1 to Lean 4
(the spike in `compat/verdi/` already ports the entire handler layer,
builds clean, and proves first lemmas), and the only battle-tested
*checkable*-correspondence pattern (Theorem's lf-lean / rocq-lean-import) fits
our shape exactly. The honest hard parts are (a) the correspondence
*certification* toolchain and (b) the protocol gap between verdi-raft's 2016
protocol and etcd-io/raft — not the port.

Relation to prior record: this extends `docs/2026-08-08_verdi-parity-backlog.md`
(embedding Verdi's network semantics as a second deep embedding) from
"parity of statements" to "identity of specs, with a machine-checked bridge."
Target-theorem sizing context: TODO F5.

---

## 1. What Verdi's Raft spec actually is

Reference checkouts (gitignored `deps/`, clone-yourself; pins as read today):
`deps/verdi` @ `7e1641b` (maintained, 2026-01), `deps/verdi-raft` @ `a3375e8`
(last commit 2023-12), `deps/StructTact` @ `97268e1`.

The spec is small and cleanly layered:

- **System model** (`deps/verdi/theories/Core/Net.v`): typeclasses
  `BaseParams` (data/input/output, `Net.v:12`), `OneNodeParams` (the machine
  being replicated, `Net.v:19`), `MultiParams` (names, msgs, finite node list,
  `net_handlers`/`input_handlers` as **pure functions**
  `… → data → list output * data * list (name * msg)`, `Net.v:31-43`),
  `FailureParams` (`reboot`, `Net.v:45`). Network = packet bag + per-node
  state (`Net.v:310-321`); step relations `step_async`/`step_dup`/`step_drop`
  and **`step_failure`** (deliver/input/drop/dup/crash/reboot,
  `Net.v:420-459`) — the fault model all headline theorems assume. Traces
  record external I/O only.
- **Raft instance** (`deps/verdi-raft/theories/Raft/RaftState.v:15-38` +
  `Raft.v:9-513`): a 14-field state record (one **ghost** field,
  `electoralVictories`); 4 message constructors; ~400 lines of handler
  algorithms (`handleAppendEntries`, `handleRequestVote`, `doLeader`,
  `doGenericServer`, …) composed into `RaftNetHandler`/`RaftInputHandler`;
  `reboot`/`init_handlers`; the three instances. Everything is first-order
  pure functional programming over `nat`/`bool`/`list`/records/`option` —
  no dependent types beyond `fin N`, no tactics-in-terms beyond eq-decs.
- **Statement glue**: `raft_intermediate_reachable` (`Raft.v:515-554`),
  `commit_recorded` (`CommonDefinitions.v:102`).
- **Headline theorems** (statements only; proofs are ~37k lines we do NOT
  ingest, ratio ≈ 1:60):
  - *State machine safety* (`StateMachineSafetyInterface.v:8-36`): committed
    entries agree at equal indices, over `raft_intermediate_reachable`.
    **Statement needs only the raw handlers + step relations** — no ghost
    machinery.
  - *End-to-end linearizability* (`RaftProofs/EndToEndLinearizability.v:471-478`):
    every `step_failure` trace is equivalent to a sequential execution
    (`step_1_star`) of the replicated machine. Statement needs +≈250 lines
    (`Linearizability.v:7-270`, `RaftLinearizableProofs.v:26-93`).
  - *Leader completeness* is the one headline whose **statement** requires the
    ghost/refinement layer (`refined_raft_intermediate_reachable`) — defer.

**Smallest ingestible slice:** Net.v core (~150 lines) + StructTact shims
(~100) + RaftState + Raft.v handlers (~450) + statement glue (~50), optional
linearizability defs (~250). ≈900 lines of Coq total.

## 2. The spike (done, builds clean)

`compat/verdi/` — a standalone Lake package on the repo toolchain
(`v4.31.0`), **not referenced by the root lakefile**; `lake build` in that
directory: zero errors, zero warnings. Contents:

| File | Ports | Notes |
|---|---|---|
| `VerdiCompat/StructTactPrelude.lean` | `update`, `assoc*`, `dedup`, `List.remove`, `all_fin`(+2 lemmas) | each def cites its StructTact source lines |
| `VerdiCompat/Net.lean` | params classes, packet/network, `step_1`, `step_async/dup/drop/failure` + closures | full slice needed by the theorems |
| `VerdiCompat/RaftState.lean` | the 14-field record | setter boilerplate subsumed by `{s with …}` |
| `VerdiCompat/Raft.lean` | **the entire `Raft.v:9-554` spec**: all handlers, instances, `raft_intermediate_reachable` | per-def source-line citations |
| `VerdiCompat/CommonDefinitions.lean` | statement vocabulary: `entries_match`, `sorted`, `commit_recorded`, … | `CommonDefinitions.v` slice |
| `VerdiCompat/Properties.lean` | **the consensus property statements**: `one_leader_per_term`, `log_matching`, `state_machine_safety` + named transfer targets | ghost-free headliners, 1:1 |
| `VerdiCompat/ProofStructure.lean` | **the proof scaffold, RE-PROVED**: the 11 `raft_net_invariant_*` obligation shapes, both dispatcher lemmas, THE `raft_net_invariant` induction principle, and the `step_failure_star → raft_intermediate_reachable` bridge | `Raft.v:556-848`; statements 1:1, proofs from scratch (Ltac doesn't port) |
| `VerdiCompat/Examples.lean` | non-vacuity witness: counter machine, N=3, handler runs checked by `rfl` | mirrors the repo witness doctrine |
| `AxCheck.lean` | `#print axioms` audit script | run: `env LEAN_PATH=.lake/build/lib/lean lean AxCheck.lean` |

Proved so far: `reboot_init_handlers`, `reboot_idem` (rfl, same as Coq),
`allFin_all`/`allFin_NoDup` (discharging the `MultiParams` obligations), a
real case-analysis lemma `handleRequestVote_grant_votedFor`, and — the
substantive one — **`raft_net_invariant`**, the induction principle every one
of verdi-raft's ~90 invariant proofs instantiates (one obligation per
handler + init/packet-subset/reboot), plus the trace bridge
`step_failure_star_raft_intermediate_reachable`. Axiom audit:
`propext`/`Quot.sound` only — no `sorry`, no `Classical.choice`, no
`native_decide`, and the port is total (structural recursion throughout,
matching Verdi's `Fixpoint`s).

Porting friction worth recording (bit during the proof, all benign but each
a must-know for the correspondence contract): Lean's `++` is
left-associative where Coq's is right-associative (or-tree shapes under
`In`/`∈` differ); projection-of-literal doesn't reduce syntactically for
`rw` (bridge with `show`); Coq's `in_crush` becomes explicit `rcases`
or-shuffles (core Lean has no `tauto`).

**Mapping decisions** (the systematic transformations a future mechanical
check must account for — this table IS the informal translation contract):

1. Coq typeclasses → Lean classes; sumbool eq-decs → `DecidableEq` fields with
   `@[reducible] instance` projections. Verdi's `Instance`s (`base_params`
   etc.) → `@[reducible] def`s used explicitly (no global instances).
2. StructTact `fin N` (an `option`-nesting encoding) → Lean `Fin N`;
   `all_fin` ported verbatim under the evident isomorphism. This is the one
   deliberate representation change.
3. Coq left-assoc tuples `A * B * C` → Lean right-assoc `A × B × C`
   (components identical).
4. Generated record setters / `{[ st with … ]}` → native `{ st with … }`;
   nested-setter chains flattened only where every RHS reads the original
   state (verified case by case).
5. Boolean comparison notations (`>?` etc.) kept as scoped notations over
   `Nat.blt`/`Nat.ble` — the spec stays boolean, as in Coq. `div2` ported
   verbatim (not mapped to `Nat.div2`).
6. Coq `if` on `option` (`Raft.v:258`) → explicit `.isNone` (commented at the
   port site). Coq `List.remove` (removes all) → own `removeAll`, NOT Lean's
   `List.erase` (first only) — a silent-drift trap avoided.
7. Shadowing `let state := …` kept verbatim; proofs cross it with a zeta step
   (`simp only [] at h`).

## 3. Ingestion / correspondence paths (ranked)

Context: **rocq-dove is not public.** Theorem's pipeline (per their blog +
public artifacts): author the Lean translation, `lean4export` it, kernel-import
it into Rocq via `rocq-lean-import`, and have the **Rocq kernel** check a
generated "typewise isomorphism" theorem relating original and import. The two
public pieces are `deps/rocq-lean-import` @ `96686c4` (theorem-labs fork of
rocq-community; consumes the *older text* export format, pinned lean4export
`c9f8373`) and `deps/lf-lean` @ `2c0d52e` (1,276 verified LF translations —
worked examples of the iso pattern: `Iso`/`rel_iso` in
`lf/theories/IsomorphismDefinitions.v`, per-def commutation squares, Checker
modules whose transparent ascription is the kernel check). TCB notes: Rocq
kernel in a nonstandard mode (SProp + `Definitional UIP` + per-inductive
elimination-check relaxation), lean4export, the plugin's name mapping, and the
*generated iso statements* themselves (a statement-TCB question, audit like law
statements). Version pins are the sharp constraint: Rocq 9.1-fork or 9.3-dev,
Lean 4.26-era for the export step (our port would need to also compile there —
or we pin a dedicated export toolchain).

Ranked (agent report, verified against the checkouts):

1. **Hand/LLM port + rocq-lean-import-checked iso** (the lf-lean pattern,
   self-hosted). Only path with prior art at exactly our shape. Iso statements
   are hand-written but mechanical (~1-3 lines/def); step-relation isos are
   the hardest class. Est. ~1wk toolchain + 1-2wk proofs, one-time per spec
   version. Direction of trust: Rocq kernel checks that OUR Lean spec ≅
   THEIR Rocq spec — exactly the "our spec is the same as theirs" claim.
2. **Differential execution as the cheap early oracle**: Verdi handlers are
   pure and executable — fuzz Rocq (extraction/`native_compute`) vs Lean
   (`#eval`) over generated inputs, seed-deterministic, in our existing
   harness style (and grossmith's). Not a proof, but a real oracle for the
   function fragment, available *now* with zero toolchain risk. Does not
   cover the inductive step relations.
3. **Paper adequacy argument alone** — rejected as a terminal state
   (self-certification); acceptable only as the interim state of (1) with (2)
   attached.
4. Waiting for Babel-formal / Dedukti / rocq-dove publication — no; none
   offers a checkable Rocq→Lean correspondence today, and rocq-dove's
   non-public part (statement generation) is cheap to replicate by hand at
   our scale.

Stdlib design point: lf-lean's pattern uses *mirror* inductives (their own
`nat`/`list` in Lean). The spike instead uses **Lean-native `Nat`/`List`/
`Fin`** — better for golean integration; costs slightly more Rocq-side iso
work (kernel-level they're the same zero/succ, nil/cons shapes). D2 below.

## 4. Our side: attachment points (from the golean-side survey)

Where golean is today (all verified in-tree): headline theorems are
first-order readouts over pinned lowerings (`GoldenQuorumWP/All`); the
∀-config `committedIndexAllConfigs` is "Verdi results on real code" instance
#1; `GoInvariant` is already documented as Verdi-style invariance;
channels/goroutines/select landed; **no network model, no refinement/
simulation framework, no trace semantics** (F5 unbuilt); frontend can't yet
export `raft.go` (multi-package, protobuf, stdlib externs, `sync`) — the long
pole for anything touching the real `Step`.

Three architectures, not mutually exclusive:

- **A. Spec-to-spec** (nearest-term, Go-independent): the ingested Verdi spec
  (this spike) becomes a reference object; our own declarative Raft spec is
  proven equivalent to it as pure math; Verdi's invariant stack transfers by
  transport. Can start now; is exactly the verdi-parity-backlog route
  upgraded from "comparable statements" to "provable equivalence".
- **B. Direct refinement**: per-handler forward simulation — every terminating
  GoCore run of lowered `raft.Step(m)` from a heap encoding abstract state
  `s` lands in an encoding of some `s'` with `verdiStep s m s'` (the ingested
  spec *is* the abstract object). Statement-TCB-cleanest; needs the
  refinement framework + abstraction-function layer + frontend export of
  raft.go.
- **C. WP-per-handler + abstract network shell**: `GoFuncSpec` contracts per
  message type; the N-node system is the abstract (Verdi-shaped) transition
  system whose node-step is the contract; Verdi's network nondeterminism
  (reorder/drop/dup) enters as Choices-site envelopes per the nondeterminism
  doctrine. Most incremental; each handler contract is quorum-pilot-sized.

Note A feeds both B and C: in all three the ingested spec is the abstract
side. Verdi's `step_dup`/`step_drop`/`step_failure` family maps naturally
onto the F5 envelope structure (as the backlog doc predicted).

## 4b. Statement identity and proof-structure import (user questions, 2026-08-09)

**"Is the statement of the consensus property the same as ours?"** As of this
arc, golean has NO Raft consensus statement — F5 (`TODO.md`) plans to target
exactly Verdi's stack, so identity was intended but never made inspectable.
The spike closes that: `Properties.lean` now states `one_leader_per_term`,
`log_matching`, and `state_machine_safety` in Lean, 1:1 with Verdi's
ghost-free interface files, as named transfer targets
(`StateMachineSafetyStatement` etc.). When our own spec-side statements get
written, "same property?" is a side-by-side reading of two Lean `Prop`s —
or a lemma. Two structural notes: (i) Verdi's statements quantify over
`raft_intermediate_reachable` — a spec-level reachability, which composes
with our statement-TCB doctrine by sitting on the abstract side of the
refinement, with the Go-side hypothesis remaining an interpreter-run
equation; (ii) their traces record external I/O only — same observation
philosophy as ours. Leader completeness is the one headliner whose
statement needs their ghost layer; deferred, revisit if we want it.

**"Prove the same property over a richer model, importing the Verdi proof
structure — feasible?"** Yes, with a precise meaning of "import". What
imports is the *architecture*, not the Ltac: (1) the handler-indexed
induction principle — **now proved in Lean**
(`ProofStructure.lean:raft_net_invariant`), so "invariant of the reachable
set" reduces to one obligation per handler exactly as in Verdi; extending
the model (new message types, new handlers) = extending the obligation
list; (2) the invariant DAG — verdi-raft's ~90 named invariant interfaces
(~3.5k lines of statement text, same easy-port class as the handlers) form
the roadmap of *which* invariants to prove in *what* order; that dependency
structure is the hard-won knowledge, and it ports as statements. The ~37k
lines of Ltac do NOT port — proofs over the richer model are re-proved in
Lean (where they must be redone anyway, since a richer model changes them).
Cost scales with the feature: PreVote is modular (new message pair, new
obligations, election-safety argument locally adjusted); fast nextIndex
backoff is leader-bookkeeping, safety-neutral; snapshots/compaction touch
the log representation and hence most log invariants (substantial);
**membership change invalidates the fixed-quorum arguments**
(`div2`-majorities baked into `wonElection`/`haveQuorum` and every quorum
lemma) — that one is research-grade, sequence it last or out of scope.

## 4c. The decided architecture (user direction, 2026-08-09)

The chain: **real etcd-io/raft ⟷ golean model (frontend + GoCore) ⟷
Verdi-style + extensions model in Lean ⟷ consensus proof in Lean.**

- Left link: the existing pipeline (frontend export of raft.go — the known
  long pole) plus per-handler refinement in the `IsCommittedIndex` style:
  every terminating GoCore run of a lowered handler lands in the abstract
  step (architecture B/C of §4).
- Middle object: the abstract model, SEEDED by this port and extended
  toward etcd (D4 resolved: **downscope** — the model covers the core
  fragment first; extensions added ring by ring with the ledger in §5).
- Right link: safety proved natively in Lean over that model via the
  imported proof structure (§4b); the unmodified-core port can additionally
  get its properties by P2 certificate transfer instead of re-proof.
- The Verdi compat layer's role in the chain: the anchor proving the
  middle object's core is *the* spec a published machine-checked proof
  holds of — not an artifact of our own assumptions.

## 5. The protocol-gap ledger (the honest risk)

verdi-raft (2016) vs etcd-io/raft — visible in the spec, must be tracked
explicitly if theorem transfer to real Go is the goal:

**Absent in Verdi:** PreVote; learners / ANY membership change (fixed
`fin N`); snapshots / log compaction; CheckQuorum / leader lease; ReadIndex;
leader transfer; fast nextIndex conflict backoff (theirs decrements by 1,
`Raft.v:241`); separate heartbeat message; batching/flow control.
**Representation deltas:** log stored newest-first; client identity embedded
in every entry; "sticky leader" vote guard (refuses to vote while a known
`leaderId` exists, `Raft.v:258` — deviates from the paper); ghost
`electoralVictories` inside the real state record.

Consequence: a Verdi-derived spec covers the **core-consensus fragment** of
etcd-io/raft only. That is still exactly the fragment whose safety argument
is hard and famous; but "prove the real Go vs. their spec" must be scoped as
"prove the core fragment, with a maintained delta ledger" — or the ingested
spec serves as the *anchor* for our own extended spec, with the extension
audited separately (D4).

## 6. Proposed phasing

- **P0 (done, this worktree):** research + full handler-layer port + witnesses.
- **P1 — complete the ingestible slice:** statement glue (`commit_recorded`,
  the state-machine-safety property text), linearizability defs; state
  `state_machine_safety` in Lean over the ported spec as the transfer target.
  Add the **differential-execution harness** (path 2 above): extracted-Verdi
  vs Lean `#eval` over seed-deterministic handler inputs. Pure Lean + one
  opam/extraction step; no exotic toolchain.
- **P2 — correspondence certification:** stand up the pinned
  rocq-lean-import toolchain (opam/Docker, needs network + user sign-off on
  version pins per the trust-tools rule); write Interface/Checker-style iso
  statements for the ported defs; prove them in Rocq. Deliverable: a
  Rocq-kernel-checked certificate `VerdiCompat ≅ verdi-raft`, with
  `Print Assumptions` output pinned into the repo.
- **P3 — attachment:** pick A/B/C mix once F5 (network model) and the
  frontend raft.go gaps have owners; the ingested spec is the abstract object
  in every variant, so P1/P2 are not throwaway under any choice.

## 7. Decisions for the user (D1-D5)

- **D1 — home:** keep `compat/verdi` as a standalone package, or move
  under `proofs/` once it stops being exploratory? (Standalone keeps the main
  gate untouched; integration lets golean theorems import the spec.)
- **D2 — stdlib strategy:** Lean-native `Nat`/`List`/`Fin` (spike's choice;
  better golean ergonomics, slightly heavier Rocq-side isos) vs lf-lean-style
  mirror types (verbatim pattern reuse)?
- **D3 — certification timing:** invest in the P2 toolchain now, or run
  P1-differential-only until the port stabilizes?
- **D4 — RESOLVED (user, 2026-08-09): downscope.** Core-fragment first with
  the §5 delta ledger; the ingested spec seeds the extended model per the
  §4c chain. Remaining sub-question: which extension ring comes first
  (suggest: fast backoff + heartbeat-message alignment, then PreVote;
  snapshots later; membership change last/out-of-scope).
- **D5 — ghost field:** keep `electoralVictories` (1:1 fidelity, iso is
  trivial) or drop it (cleaner spec, breaks 1:1)? Spike keeps it.

## 8. Artifacts

- This note.
- `compat/verdi/` — the spike package (builds clean on `v4.31.0`).
- New reference checkouts (clone-yourself, gitignored): `deps/verdi-raft`,
  `deps/StructTact`, `deps/rocq-lean-import`, `deps/lf-lean` (+ existing
  `deps/verdi` conventions) — CLAUDE.md's checkout list should gain these on
  merge.
- Research reports (agent runs, 2026-08-09) synthesized above; primary-source
  citations retained inline.
