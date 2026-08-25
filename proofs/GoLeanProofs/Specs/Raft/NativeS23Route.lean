import GoLeanProofs.Specs.Raft.NativeObligations

/-! # SC1 — the S2/S3 route skeleton (checker census, needed
invariants, commit-axis obligations, the leading route's statement
chain)
(scoping lane `campaign-arc4b`, 2026-08-26; SC1 charter item 1;
frame: the family route b′, design of record §8 D2 revised.)

## 1. The checker census (charter 1a — the exact S2/S3 code)

The twin checker's S2/S3 span is `tools/raftsubject/twin-lib.go`
`apply` (lines 298–335), called per committed entry from `harvest`'s
apply loop (289–291). Exactly:

- **S3 monotonicity** (302–312), PER NODE, over the apply SEQUENCE:
  `idx > nd.applied` (strictly increasing applied index) and
  `trm ≥ nd.lastTrm` (non-decreasing applied term), where
  (idx, trm) = (e.Index, e.Term) of the applied entry.
- **S3 anomaly** (313–317): `e.Type == EntryNormal`, else violation.
- **S2 agreement** (325–334), CROSS-NODE, over non-empty EntryNormal
  entries only (319–321 skips the noop): the global map
  `byIndex : index ↦ (term, data, firstNode)` — a later apply at a
  recorded index must match `(term, data)` exactly.
- S1 rides in `harvest` (268–279), S4 in `complete()` (520–529) —
  not this file's.

Fields consumed: Index/Term/Data/Type of COMMITTED-then-applied
entries; nothing else. Indexes: raft log indexes (the snapshot seeds
index 1, twin-lib.go:198-202).

## 2. The minimal abstract invariants (charter 1b)

The false-delta of each check needs, over specRound traces:

- **S2** ⇐ `state_machine_safety_host` restricted to non-empty
  normal entries (T3 statement: `VerdiCompat/Properties.lean:83`,
  STATEMENT-ONLY in T3 — no proof exists in the tree): any two
  applied entries at the same index agree on (term, data).
- **S3-index** ⇐ a LOCAL Ready-machinery fact: applied entries are
  delivered in strictly increasing index order
  (`nextCommittedEnts` returns the (applying, maxAppliable] slice in
  log order — raftsubject/raft/log.go:220-244; `appliedTo` enforces
  prevApplied ≤ i ≤ committed — log.go:332-336).
- **S3-term** ⇐ per-node LOG term-monotonicity (entries sorted by
  index have non-decreasing terms) + S3-index + applied-from-log.
- **S3-anomaly** ⇐ entry PROVENANCE: every entry in any log /
  in-flight append is EntryNormal (the driver proposes only normal
  commands; the noop is EntryNormal with empty data — raft.go:980-81).

## 3. The commit-axis check against the signature (charter 1c,
re-targeted per D2-revised)

VERIFIED at the statement level: the S2/S3-needed invariants consume
the commit axis ONLY through the three commit obligations below
(`CommitObligations`) — never through any dialect's commit RULE:

- S2's chain needs applied ⊆ committed ⊆ certified-agreed prefix:
  `commitCertified` (O-C2/O-C3) + `commitMono` (O-C1) +
  `appliedWindow`. The A4 mismatch axis (commit-advance without new
  entries) DISSOLVES here: both dialects' rules are members of the
  O-C3 envelope — proved below (`etcd_emptyAccept_discharges` /
  `verdi_frozen_discharges`, the vacuity-discipline demonstrator:
  same obligation, visibly different implementations).
- S3's chain needs only `commitMono` + `appliedWindow` + the local
  apply-order fact — no commit RULE at all.
- The ONE caveat, named: etcd's heartbeat commit
  (raft.go:1854-55 `commitTo(m.Commit)`, unguarded locally) discharges
  O-C3 only through the leader-side send bound
  (`min(match[to], committed)`), which needs a leader match-soundness
  invariant — an extra signature member IF heartbeat rounds are ever
  reachable. For T1 they are NOT (the D3 reachability refutation:
  ticks never driven), so the member is deferred, recorded here.

## 4. The route verdict input (charter 1d — sizing, in the log)

T3 proves NOTHING above `one_leaderLog_per_term`
(`VerdiCompat/LeaderLogs.lean:31-33`: `leader_completeness` is
"defs only; its proof is a later arc's"; log_matching /
state_machine_safety are statements in `Properties.lean`). So for
S2 there is no lattice proof to port or project — EVERY route builds
the S2 superstructure NEW. The b′ frame makes that superstructure
family-level (proved from the obligations once, both dialects
discharge); the T1-scoped chain below (§5) is the small variant that
consumes the driver shape. Full sizing + recommendation:
`docs/campaign-arc4b-log.md`.

LINEAGE: history/auxiliary variable refinement (Abadi–Lamport) for
the ghost history `H`; the S2 leaf is property transfer through the
refinement mapping (the classic, design §4). -/

namespace GoLean.RaftSeam.NativeSpec

/-! ## The commit-axis obligation members (the signature's S2/S3
fragment). Stated over the etcd-abstract node (`ENode`) plus an
abstract certification predicate — the per-dialect discharge notes
name the concrete rule sites. -/

/-- The follower commit-advance envelope (O-C3): on accepting an
append whose previous-entry match is certified at `matched`, the new
commit is exactly `max committed (min leaderCommit matched)` — or
anything BELOW that bound and above the old commit. Both dialects'
rules are members:
- etcd: `commitTo(min(committed, lastnewi))` on EVERY accepted
  MsgApp including empty/duplicate (raftsubject/raft/log.go:129) —
  the SUPREMUM of the envelope;
- Verdi: commit frozen on empty accepts (`haveNewEntries` guards —
  `VerdiCompat/Raft.lean:169-201`, the C1 probe's
  `verdi_emptyAE_commit_frozen`) — the INFIMUM.
The A4 kill-point (`adapter_hb_advance_mismatch`) was the statement
that these two POINTS differ; at the obligation level both discharge. -/
def followerCommitOk (committed leaderCommit matched committed' : Nat) :
    Prop :=
  committed ≤ committed' ∧
  committed' ≤ max committed (min leaderCommit matched)

/-- The etcd empty-accept delta (log.go:129 at `lastnewi = matched`,
the A4 mismatch witness family HhAdv/empty-MsgApp). -/
def etcdEmptyAcceptCommit (committed leaderCommit matched : Nat) : Nat :=
  max committed (min leaderCommit matched)

/-- **PROVED (vacuity-discipline demonstrator, etcd half)**: etcd's
commit-advance-without-new-entries discharges O-C3. -/
theorem etcd_emptyAccept_discharges (c lc m : Nat) :
    followerCommitOk c lc m (etcdEmptyAcceptCommit c lc m) :=
  ⟨Nat.le_max_left .., Nat.le_refl _⟩

/-- **PROVED (vacuity-discipline demonstrator, Verdi half)**: Verdi's
frozen commit discharges the SAME obligation — the two dialects sit
at opposite ends of one envelope, which is the b′ dissolution of the
A4 mismatch (the mismatch was real only against Verdi's POINT rule,
not against the family obligation). -/
theorem verdi_frozen_discharges (c lc m : Nat) :
    followerCommitOk c lc m c :=
  ⟨Nat.le_refl _, Nat.le_max_left ..⟩

/-- The leader commit-advance obligation (O-C2): the leader commits
only to a quorum-certified index bearing its own term.
- etcd discharge: `maybeCommit` (raft.go:794-98) commits to
  `trk.Committed()` (the quorum majority of match indexes,
  raftsubject/quorum/majority.go `CommittedIndex`) guarded by
  `matchTerm{term: r.Term}` (log.go:455-462);
- Verdi discharge: `advanceCommitIndex`'s quorum-of-matchIndex rule
  (deps/verdi-raft; the T3 lattice's leader-commit site).
`certified` abstracts "a quorum of nodes has acknowledged the prefix
through idx with the leader's term at idx" — its concretization (the
match-evidence invariant) is the S2 wave's first NEW signature
member. -/
def leaderCommitOk (certified : Nat → Prop)
    (committed committed' : Nat) : Prop :=
  committed ≤ committed' ∧ (committed' = committed ∨ certified committed')

/-- The commit guard obligation (O-C1): commit never decreases and
never passes the log end. etcd discharge: the `commitTo` guard
(log.go:322-330: never decrease; panic past lastIndex — panics are
outside the completing-run envelope). Verdi discharge:
`min(leaderCommit, maxIndex log'')` by construction. -/
def commitInWindow (committed logLen committed' : Nat) : Prop :=
  committed ≤ committed' ∧ committed' ≤ logLen

/-- The apply window (`appliedTo`, log.go:332-336: prevApplied ≤ i ≤
committed; `nextCommittedEnts`' slice bounds, log.go:220-244). -/
def appliedWindow (applied committed applied' : Nat) : Prop :=
  applied ≤ applied' ∧ applied' ≤ committed

/-! ## §5 The leading route's statement chain (T1-scoped ghost
history — each Prop is a chain link; classifications vs T3: ALL NEW
(no T3 proof exists above `one_leaderLog_per_term`), but
obligation-consuming (family-reusable) except where marked
driver-shaped. The chain's sizing ledger is the log's. -/

/-- The ghost history: the (index, term, dataId) sequence the single
reachable election's leader drives. Position k holds index k+1
(the twin's snapshot seeds index 1 — twin-lib.go:198-202: H's head is
the snapshot entry (1, 1, noop)). -/
abbrev Hist := List (Nat × Nat × Nat)

/-- History lookup by raft index. -/
def histAt (H : Hist) (idx : Nat) : Option (Nat × Nat × Nat) :=
  if idx = 0 then none else H[idx - 1]?

/-- CHAIN LINK H1 (NEW, driver-shaped; consumes O4/leaderEntry + the
single-campaign driver fact): at most one election happens, its
winner is node 1, and `H` is written only by node 1's propose/noop
appends — `H` is append-only along every trace. -/
def Skel_singleWriterHistory (_step Reach : SNet → SNet → Prop)
    (histOf : SNet → Hist) : Prop :=
  ∀ N₀ N N', Reach N₀ N → Reach N₀ N' →
    (∃ H'' : Hist, histOf N' = histOf N ++ H'') ∨
    (∃ H'' : Hist, histOf N = histOf N' ++ H'')

/-- CHAIN LINK H2 (NEW, family-shaped; consumes leader-only-append at
own term — the signature's append obligation, with the noop entry as
an instance): `H` is index-consecutive and term-monotone. -/
def Skel_histWellFormed (Reach : SNet → SNet → Prop)
    (histOf : SNet → Hist) (N₀ : SNet) : Prop :=
  ∀ N, Reach N₀ N →
    (∀ (k : Nat) (e : Nat × Nat × Nat),
      (histOf N)[k]? = some e → e.1 = k + 1) ∧
    (∀ (k k' : Nat) (e e' : Nat × Nat × Nat), k ≤ k' →
      (histOf N)[k]? = some e → (histOf N)[k']? = some e' →
      e.2.1 ≤ e'.2.1)

/-- CHAIN LINK H3 (NEW, family-shaped; consumes the append/truncation
obligations — truncation-on-conflict never fires on the single-leader
reachable set, but the LINK's statement doesn't assume that; its
PROOF consumes H1): every node's log is a prefix of `H`, and every
in-flight append payload is an `H`-slice anchored at its certified
previous entry. -/
def Skel_logsArePrefixes (Reach : SNet → SNet → Prop)
    (histOf : SNet → Hist) (logOf : SNet → Nat → Hist) (N₀ : SNet) :
    Prop :=
  ∀ N, Reach N₀ N → ∀ i,
    ∃ rest : Hist, histOf N = logOf N i ++ rest

/-- CHAIN LINK H4 (NEW, family-shaped; consumes O-C1/O-C2/O-C3 +
`appliedWindow`): every APPLIED entry of every node equals the
`H`-entry at its index. (The commit axis enters the chain here and
ONLY here — the §3 verification.) -/
def Skel_appliedFromHist (Reach : SNet → SNet → Prop)
    (histOf : SNet → Hist)
    (appliedOf : SNet → Nat → List (Nat × Nat × Nat)) (N₀ : SNet) :
    Prop :=
  ∀ N, Reach N₀ N → ∀ i e, e ∈ appliedOf N i →
    histAt (histOf N) e.1 = some e

/-! ### PROVED (the S2 leaf assembly): H4 implies the S2 checker's
false-delta — two applied records at one index agree, because both
equal the history's entry. The checker-implication leaf is then this
lemma transferred through `absTwinRead` (the C-wave's round-lemma
work, not SC1's). -/

theorem s2_agree_of_hist {H : Hist} {e e' : Nat × Nat × Nat}
    (he : histAt H e.1 = some e) (he' : histAt H e'.1 = some e')
    (hidx : e.1 = e'.1) : e = e' := by
  rw [hidx] at he
  rw [he] at he'
  exact Option.some.inj he'

/-! ### PROVED (the S3-term leaf assembly): history term-monotonicity
plus apply-from-history plus increasing apply indexes give the
checker's non-decreasing applied terms. -/

theorem s3_term_of_hist {H : Hist}
    (hwf : ∀ (k k' : Nat) (e e' : Nat × Nat × Nat), k ≤ k' →
      H[k]? = some e → H[k']? = some e' → e.2.1 ≤ e'.2.1)
    {e e' : Nat × Nat × Nat}
    (he : histAt H e.1 = some e) (he' : histAt H e'.1 = some e')
    (hlt : e.1 ≤ e'.1) : e.2.1 ≤ e'.2.1 := by
  unfold histAt at he he'
  by_cases h0 : e.1 = 0
  · simp [h0] at he
  by_cases h0' : e'.1 = 0
  · simp [h0'] at he'
  rw [if_neg h0] at he
  rw [if_neg h0'] at he'
  exact hwf (e.1 - 1) (e'.1 - 1) e e' (Nat.sub_le_sub_right hlt 1) he he'

end GoLean.RaftSeam.NativeSpec
