import VerdiCompat.Raft
open VerdiCompat VerdiCompat.Raft
set_option maxHeartbeats 1000000 in
example {P : BaseParams} [R : RaftParams P] (me : name (P := P)) (st : raft_data (P := P))
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) {st' m}
    (h : handleAppendEntries me st t lid pli plt es ci = (st', m)) :
    True := by
  unfold handleAppendEntries at h
  split at h
  · trivial
  · split at h
    · trivial
    · trivial
