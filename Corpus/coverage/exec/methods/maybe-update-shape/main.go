package main

// CL1 (window charter §4.1; docs/2026-10-03_window-corpus-disposition.md):
// the customer's `Progress.MaybeUpdate` shape (raftsubject/tracker/
// progress.go:205) on a miniature multi-field record. A pointer-receiver
// method called directly; a stale/equal guard that returns false and
// leaves the record unchanged; declared-width fields (uint64, uint8,
// int32); `max(pr.Next, n+1)` with the uint64 wrap at n = 2^64-1; an
// unrelated field and a second instance framed; two successive calls
// observed after each. A miniature fixture is NOT a proof of Raft.

type window struct {
	start, count int
}

type progress struct {
	Match, Next      uint64
	MsgAppFlowPaused bool
	State            uint8
	Gen              int32
	Ins              window
}

func (pr *progress) MaybeUpdate(n uint64) bool {
	if n <= pr.Match {
		return false
	}
	pr.Match = n
	pr.Next = max(pr.Next, n+1) // invariant: Match < Next
	pr.MsgAppFlowPaused = false
	return true
}

func snap(pr *progress) uint64 {
	p := uint64(0)
	if pr.MsgAppFlowPaused {
		p = 1
	}
	return pr.Match*1000000 + pr.Next*1000 + p*100 + uint64(pr.State)*10 + uint64(pr.Gen)
}

// Two successive calls with inputs a then b; each result and the
// record after each call is observed; `other` must stay framed.
func maybeUpdateTwice(a, b int) (bool, uint64, bool, uint64, uint64, int, int) {
	pr := &progress{Match: 3, Next: 7, MsgAppFlowPaused: true, State: 2, Gen: 5, Ins: window{start: 1, count: 2}}
	other := progress{Match: 3, Next: 7, MsgAppFlowPaused: true, State: 2, Gen: 5}
	r1 := pr.MaybeUpdate(uint64(a))
	s1 := snap(pr)
	r2 := pr.MaybeUpdate(uint64(b))
	s2 := snap(pr)
	return r1, s1, r2, s2, snap(&other), pr.Ins.start, pr.Ins.count
}

// n = 2^64-1: n+1 wraps to 0, so max(Next, 0) keeps Next.
func maybeUpdateWrap() (bool, uint64, uint64, bool) {
	pr := &progress{Match: 1, Next: 9, MsgAppFlowPaused: true}
	r := pr.MaybeUpdate(^uint64(0))
	return r, pr.Match, pr.Next, pr.MsgAppFlowPaused
}

// Declared widths wrap in their own type; a copied struct field is
// independent of the record it was read from.
func fieldWidthsAndCopy() (uint8, int32, int, int, int) {
	pr := progress{State: 255, Gen: 2147483647, Ins: window{start: 4, count: 1}}
	pr.State++
	pr.Gen++
	w := pr.Ins
	w.start = 9
	pr.Ins.count += 10
	return pr.State, pr.Gen, pr.Ins.start, pr.Ins.count, w.count
}

func main() {
	println(maybeUpdateTwice(5, 3))
	println(maybeUpdateWrap())
	println(fieldWidthsAndCopy())
}
