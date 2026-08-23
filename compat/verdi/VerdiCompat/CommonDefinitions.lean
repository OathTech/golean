import VerdiCompat.Raft

/-!
# verdi-raft's common statement vocabulary (slice)

1:1 port of the slice of `deps/verdi-raft/theories/Raft/CommonDefinitions.v`
needed to STATE the headline safety properties (`commit_recorded` and the
predicates the log-matching statement uses) plus — P1 — the execute/dedup
slice the linearizability statement's witness vocabulary lives in
(`applied_entries`, `execute_log`, `key`, `deduplicate_log`,
`output_correct`; `CommonDefinitions.v:27-122`), and — Arc 3 unit 10 —
`prefix_within_term` (`CommonDefinitions.v:108-114`, the
PrefixWithinTerm vocabulary; closes this header's old "still not
ported" note).
-/

namespace VerdiCompat
namespace Raft

section CommonDefs
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

/-- `CommonDefinitions.v:8-15` -/
def entries_match (entries entries' : List (entry (P := P))) : Prop :=
  ∀ e e' e'',
    e.eIndex = e'.eIndex →
    e.eTerm = e'.eTerm →
    e ∈ entries →
    e' ∈ entries' →
    e''.eIndex ≤ e.eIndex →
    (e'' ∈ entries ↔ e'' ∈ entries')

/-- `CommonDefinitions.v:17-25` (the newest-first log invariant shape) -/
def sorted : List (entry (P := P)) → Prop
  | [] => True
  | e :: es =>
    (∀ e', e' ∈ es → e.eIndex > e'.eIndex ∧ e.eTerm ≥ e'.eTerm) ∧ sorted es

/-- `CommonDefinitions.v:58-59` -/
def uniqueIndices (xs : List (entry (P := P))) : Prop :=
  (xs.map entry.eIndex).Nodup

/-- `CommonDefinitions.v:102-105` — "node `h` has committed entry `e`":
it is in `h`'s log at or below `h`'s applied/commit watermark. -/
def commit_recorded (net : Network (raft_base_params (P := P)) raft_multi_params)
    (h : name (P := P)) (e : entry (P := P)) : Prop :=
  e ∈ (net.nwState h).log ∧
  (e.eIndex ≤ (net.nwState h).lastApplied ∨
   e.eIndex ≤ (net.nwState h).commitIndex)

/-- `CommonDefinitions.v:124-127` -/
def terms_and_indices_from_one (l : List (entry (P := P))) : Prop :=
  ∀ e, e ∈ l → e.eTerm ≥ 1 ∧ e.eIndex ≥ 1

/-- `CommonDefinitions.v:108-114` (`prefix_within_term`): within one
term, `l1`'s entries at or below an `l2` entry of that term are in
`l2`. -/
def prefix_within_term (l1 l2 : List (entry (P := P))) : Prop :=
  ∀ e e',
    e.eTerm = e'.eTerm →
    e.eIndex ≤ e'.eIndex →
    e ∈ l1 →
    e' ∈ l2 →
    e ∈ l2

/-! ## The execute/dedup slice (P1) -/

/-- `CommonDefinitions.v:27-37` -/
def argmax {A : Type} (f : A → Nat) : List A → Option A
  | a :: l' =>
    match argmax f l' with
    | some a' => if f a' <=? f a then some a else some a'
    | none => some a
  | [] => none

/-- `CommonDefinitions.v:39-49` -/
def argmin {A : Type} (f : A → Nat) : List A → Option A
  | a :: l' =>
    match argmin f l' with
    | some a' => if f a <=? f a' then some a else some a'
    | none => some a
  | [] => none

/-- `CommonDefinitions.v:51-56` — the longest applied prefix in the
network, read off the node with the greatest `lastApplied` (oldest-first,
hence the `reverse` of the newest-first log). -/
def applied_entries (sigma : name (P := P) → raft_data (P := P)) :
    List (entry (P := P)) :=
  match argmax (fun h => (sigma h).lastApplied) (allFin (RaftParams.N P)) with
  | some h => (removeAfterIndex (sigma h).log (sigma h).lastApplied).reverse
  | none => []

/-- `CommonDefinitions.v:61-67` -/
def execute_log' : List (entry (P := P)) → P.data → List (P.input × P.output) →
    List (P.input × P.output) × P.data
  | [], st, l => (l, st)
  | e :: log', st, l =>
    let (o, st') := O.handler e.eInput st
    execute_log' log' st' (l ++ [(e.eInput, o)])

/-- `CommonDefinitions.v:69-70` — replay a log through the replicated
machine from its initial state. -/
def execute_log (log : List (entry (P := P))) :
    List (P.input × P.output) × P.data :=
  execute_log' log O.init []

/-- `CommonDefinitions.v:72` — client-request identity. `key_eq_dec`
(`CommonDefinitions.v:74-77`) is the derived product instance. -/
@[reducible] def key : Type := R.clientId × Nat

/-- `CommonDefinitions.v:79-80` -/
def key_of (e : entry (P := P)) : key (P := P) :=
  (e.eClient, e.eId)

/-- `CommonDefinitions.v:82-92` — client-session dedup, the pure-log
mirror of `cacheApplyEntry`'s cache: keep an entry iff its id is fresh or
strictly newer than the client's last kept id. -/
def deduplicate_log' : List (entry (P := P)) → List (R.clientId × Nat) →
    List (entry (P := P))
  | [], _ => []
  | e :: es, ks =>
    match assoc ks e.eClient with
    | some n =>
      if n <? e.eId then
        e :: deduplicate_log' es (assoc_set ks e.eClient e.eId)
      else deduplicate_log' es ks
    | none => e :: deduplicate_log' es (assoc_set ks e.eClient e.eId)

/-- `CommonDefinitions.v:94` -/
def deduplicate_log (l : List (entry (P := P))) : List (entry (P := P)) :=
  deduplicate_log' l []

/-- `CommonDefinitions.v:96-100` -/
def mEntries : msg (P := P) → Option (List (entry (P := P)))
  | .AppendEntries _ _ _ _ entries _ => some entries
  | _ => none

/-- `CommonDefinitions.v:116-122` — "output `out` for `(client, id)` is
correct given applied entries `aes`": the deduplicated log replayed up to
that client's entry produces exactly `out` last. Coq's
`hd_error (rev tr')` is `tr'.reverse.head?`. -/
def output_correct (client : R.clientId) (id : Nat) (out : P.output)
    (aes : List (entry (P := P))) : Prop :=
  ∃ xs e ys tr' st',
    deduplicate_log aes = xs ++ e :: ys ∧
    e.eClient = client ∧
    e.eId = id ∧
    execute_log (xs ++ [e]) = (tr', st') ∧
    tr'.reverse.head? = some (e.eInput, out)

end CommonDefs

end Raft
end VerdiCompat
