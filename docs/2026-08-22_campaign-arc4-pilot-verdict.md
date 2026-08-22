# Campaign Arc 4 — A4-U1 pilot verdict (2026-08-22)

Campaign lane `campaign-arc4`, [AGENT] throughout. Governing:
`docs/2026-08-22_campaign-arc4-seam-design.md` §4 (the GO signal:
"the pilot equation proves with the kit at ≤ a gallery example's
effort. Anything else → re-design here before more units").
Worked record: `docs/campaign-arc4-log.md`; modules under
`proofs/GoLeanProofs/Raft/`.

## 1. VERDICT: architecture GO, cost model NO-GO

**The equation FORM is validated end to end** — abstraction reader,
conditioned span equation over an abstract machine state, discharge
witness on the pinned program, projection readout — and **the
per-handler hand-walk cost model FAILS the seam design's bar**: the
SMALLEST handler on the census path is ~4× a gallery example's
dynamic size and hits five ingredient classes the kit has no forms
for. Do NOT dispatch A4-U2..U8 as hand-walked WP units against the
current kit; re-design per §5 below.

## 2. What the pilot proved (kernel-checked at this tip)

All in `proofs/GoLeanProofs/Raft/` (wired into the GoLeanProofs
aggregator; full proofs+Audit build green, 469 jobs). `#print axioms`
verbatim (capped `lake env lean` probe, this tip):

```
'GoLean.RaftSeam.storeTarget_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoLean.RaftSeam.alt_call_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoLean.RaftSeam.alt_call_span_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoLean.RaftSeam.alt_witness_projection' depends on axioms: [propext]
```

- `AbsState.lean` — **`absRaftNode` v1**: total, `Option`-valued,
  fail-closed reader of one node's raft-state projection
  (term/vote/lead/state + committed/applied through the `raftLog`
  pointer), grounded in the instrumented heap shape (one
  `.struct raft.raft` cell of 32 fields behind the `*raft` pointer;
  probe record in the arc log). Omissions numbered GAP-V1-1..5 in the
  docstring. Plus **`specBecomeFollower`**, the re-grounded spec
  handler (mirrors the subject exactly; its correspondence to the
  ported `advanceCurrentTerm`+Follower/lead composite is stated with
  its `st.term ≤ t` side condition — compat/verdi cited, never
  imported, per Plan A).
- `HandlerEq.lean` — **`storeTarget_field`** (the struct-field store
  form the kit lacks — kit guide §23's "struct-cell generalization,
  parked" hit on day one; closed locally, promotion-ledger row) and
  **`alt_call_span`**: the 15-step interpreter-run span equation for
  `raft.raft.abortLeaderTransfer` (the smallest callee on
  `becomeFollower`'s dynamic path) over an ABSTRACT state — symbolic
  raft-cell address, symbolic struct fields, conditioned
  `enterFrame`/lookup/set/normalize hypotheses, ten windows chained
  by `stepFnIter_chain`.
- `BecomeFollowerWitness.lean` — the §3.3 **discharge witness**:
  every premise of `alt_call_span` proved on a concrete state over
  the PINNED `twinLowered` tables (raft cell = the machine's own
  `defaultValue` at `raft.raft`), plus `alt_witness_projection`: the
  projection is live (`some ⟨0,0,0,0,0,0⟩`) and preserved across the
  call. Witness-scope caveat GAP-U1-W1: the state is
  well-formed-by-construction, not proved reachable (a reachable
  witness needs Arc-2's checkpoint reflection; raw kernel evaluation
  to the first call site at ~22k subject steps is refuted by Arc-2's
  measured ladder).

**Honest gap GAP-U1-E1 (the headline deliverable, not completed):**
the full `becomeFollower` interpreter-run equation
(`absRaftNode σ' a = some (specBecomeFollower N t l)`) is NOT proved.
Smallest reproducing goal: compose the remaining nine callee spans of
§3's table — of which `tracker.ProgressTracker.Visit`'s
choice-quantified map range (3 mapIter picks, `sort-slice`
canonicalization, three closure `call-value` entries) is the hard
core. Nothing here counts toward any total (constitution §3.6).

## 3. The measured numbers

**Dynamic contact** (compiled-interpreter probe over the pinned wire,
`artifacts/probe/trace.out`; first `becomeFollower` call, from
`newRaft`, n=3): **3,233 machine steps, 4 choices consumed, 164 fresh
cells**, ~25 frame entries. The seam design's "few-line bodies"
estimate is refuted at machine level. Per-callee (steps, choices),
derived from the same trace:

| callee | steps | choices |
|---|---|---|
| raft.raft.reset | 3,115 | 4 |
| tracker.ProgressTracker.Visit | 2,264 | 3 |
| raft.raft.resetRandomizedElectionTimeout | 640 | 1 |
| raft.lockedRand.Intn (D-11 jitter) | 605 | 1 |
| raft.raftLog.lastIndex (×3, via Visit's closure) | 331 | 0 |
| raft.newReadOnly | 66 | 0 |
| tracker.NewInflights (×3) | 59 | 0 |
| tracker.ProgressTracker.ResetVotes | 27 | 0 |
| raft.raft.abortLeaderTransfer | 17 | 0 |
| raft.Logger.Infof (harness logger, empty) | 14 | 0 |

**Proof cost of the leaf** (the pilot's measured unit): 15-step span
= 484 lines across the three modules (`wc -l`: AbsState 143,
HandlerEq 203, Witness 138), 4 theorems + 10 supporting defs;
elaboration (capped, warm oleans): AbsState + HandlerEq **< 1 s
each**; the witness module **70 s** (the pinned-table evaluations —
`enterFrame` over 867 funcs, `defaultValue`/normalization over the
twin's type table — dominate). Roughly **9 proof lines per machine
step** at the leaf, where every conditioned fact appears once.

**The bar** (seam design §4: "≤ a gallery example's effort", named
fixtures): `Examples/Fib.lean` = 1,890 lines, `Examples/MatMul.lean`
= 2,486 lines (`wc -l` at this tip).

**Extrapolation** (bound-flavored, stated as an estimate, not a
measurement): at leaf rate with loop/schema compression,
`becomeFollower` alone projects to ~3,000–6,000 lines — 1.5–3× the
bar for the CAMPAIGN'S SMALLEST handler — before the five missing
ingredient classes below, each of which is form-discovery work, not
lines. The message handlers (A4-U2..U8) are 3–10× `becomeFollower`'s
dynamic size; ~20 handlers at hand-walk cost is a 20–60
gallery-unit program. That is the NO-GO.

**Ingredient classes with no kit form** (all hit inside the smallest
handler; promotion-ledger section of the arc log):
1. struct-field stores with whole-struct re-normalization
   (`storeTarget_field` closes the store; normality-preservation
   under `StructFields.set` is still needed to DERIVE the `hnorm`
   premises in ∀-state equations);
2. closure `call-value` frame entry (`callValArgsK` — no
   `stepFn_call_enter` analogue);
3. sequential `sync-op` crossing (mutex Lock/Unlock — lockedRand,
   MemoryStorage);
4. `sort-slice` stmtOp facts;
5. choice-quantified map range at pointer-valued maps
   (`MapMem` is uint64-key/value-shaped; `trk.Progress` is
   `map[uint64]*Progress`).

## 4. Open questions, answered from contact

- **OQ-A (Option vs WF-pack): both, layered.** `absRaftNode` is an
  `Option` reader (`none` = fail closed); the equations additionally
  carry executable WF facts the projection deliberately does not
  determine (electionTimeout, tracker key set, unstable/storage
  shape) as per-equation conditioned hypotheses. Recorded in
  AbsState.lean's docstring.
- **OQ-B (do the kit's call-enter forms suffice?): fid calls yes —
  including interface dispatch**, which resolves INSIDE `enterFrame`
  and so rides the same conditioned hypothesis (`Logger.Infof`
  needs no new form). **Closure call-value entries no** — one new
  general lemma class needed (ledger item 2).
- **OQ-C (choice consumption inside handlers): the expected "none"
  is REFUTED at the smallest handler.** `becomeFollower` consumes 4
  choices: the D-11 jitter pick (`lockedRand.Intn`'s one-draw map
  range) and `Visit`'s 3 mapIter picks over `trk.Progress`. The
  equations must quantify over the consumed prefix; the post-STATE
  is choice-independent on this path (`Visit` sorts; `Intn`'s pick
  lands only in the unprojected `randomizedElectionTimeout`), so the
  seam design's "equation quantifies over the consumed prefix"
  fallback is the RULE, not the exception — with an existential
  post-state and a fixed projection.
- **OQ-D**: contact taught one scoping fact — S1 assembly needs the
  TRACKER projection (Votes/Progress — the election bookkeeping) on
  top of v1's node scalars (GAP-V1-2); detailed S2/S3 scoping stays
  with A4-U10 as chartered.

## 5. Re-design recommendation for A4-U2..U8

Keep the TARGET VOCABULARY the pilot validated — per-callee span
equations over abstract states, composed with `stepFnIter_chain`,
projections via `absRaftNode`, spec handlers re-grounded — and
change the GENERATOR:

1. **Primary: extend the symbolic evaluator to the handler fragment**
   (struct cells + field get/set with normalization, frame entry
   over pinned tables, per-branch windows, sequential sync-ops, the
   sorted map-range idiom), so per-handler equations become
   transported windows (the matmul mechanism at library scale). This
   is §5-latitude tooling investment; exec-slow is preserved — the
   evaluator ships with its refinement theorem and never enters a
   statement. Measured motivation: the leaf's conditioned facts were
   ~9 lines/step of hand labor that transport makes output-free.
2. **Convergent alternative: the W7 SpecTec route** (already recorded
   in the seam design §2(B)) — if AST-level frontend correspondence
   lands mid-campaign, handler equations derive from it rather than
   from step walks. The unit ladder should not bet against this;
   front-load whichever handlers the flagship induction needs least.
3. **Kit lifts regardless** (the arc log's promotion ledger): the
   five ingredient classes above are needed by EITHER route's
   residual obligations and by every future subject.
4. **Do not weaken the equations to make hand-walking fit** — no
   narrowed machine, no coarser projection equality; a proof wanting
   a narrower machine poses a ruling (constitution §3.4), and none
   is posed here.

The pilot's honest end state: form GO, generator NO-GO, gaps
numbered, instruments named. Re-design happens HERE (seam design §4)
before any A4-U2 dispatch.
