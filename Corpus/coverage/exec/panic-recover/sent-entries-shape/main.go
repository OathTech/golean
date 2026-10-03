package main

// CL3 (window charter §4.3; docs/2026-10-03_window-corpus-disposition.md):
// the customer's `Progress.SentEntries` shape (raftsubject/tracker/
// progress.go:165): `pr.Next += …` is written, then `Inflights.Add`
// panics on a full window, and the later `MsgAppFlowPaused` update does
// not run. The write survives (observed after recover, and in deferred
// prints of two frames on the unrecovered path); a value returned and
// printed before the failure is part of the observation; a Go `error`
// and a panic from the same call path stay distinct. A miniature
// fixture is NOT a proof of Raft.

import "errors"

type inflights struct {
	count, size int
}

func (in *inflights) Full() bool { return in.count == in.size }

func (in *inflights) Add(index uint64) {
	if in.Full() {
		panic("cannot add into a Full inflights")
	}
	in.count++
}

type progress struct {
	Next             uint64
	MsgAppFlowPaused bool
	Inflights        *inflights
}

func (pr *progress) SentEntries(entries int) {
	if entries > 0 {
		pr.Next += uint64(entries)
		pr.Inflights.Add(pr.Next - 1)
	}
	pr.MsgAppFlowPaused = pr.Inflights.Full()
}

// full=0: one free slot (normal path, the window fills, paused);
// full=1: the window is already full (Add panics after Next moved).
func sentEntriesRecovered(full int) (r string, next uint64, paused bool, count int) {
	pr := &progress{Next: 10, Inflights: &inflights{count: 1 + full, size: 2}}
	defer func() {
		if v := recover(); v != nil {
			r = v.(string)
		}
		next, paused, count = pr.Next, pr.MsgAppFlowPaused, pr.Inflights.count
	}()
	pr.SentEntries(3)
	return "returned", 0, false, 0
}

func send(pr *progress, entries int) uint64 {
	defer func() { println("send-defer next", pr.Next) }()
	pr.SentEntries(entries)
	return pr.Next
}

// Unrecovered: the first call returns and its value is printed, the
// second panics; both frames' deferred prints run during the unwind,
// innermost first, and show the surviving write (Next 16), with the
// pause flag still false.
func sentEntriesAbort() uint64 {
	pr := &progress{Next: 10, Inflights: &inflights{count: 0, size: 1}}
	defer func() { println("outer-defer next", pr.Next, "paused", pr.MsgAppFlowPaused) }()
	v := send(pr, 3)
	println("returned", v)
	pr.MsgAppFlowPaused = false
	return send(pr, 3)
}

var errCompacted = errors.New("requested index is unavailable due to compaction")

// term(i): i < 5 → the Go error errCompacted; i > 9 → a panic;
// otherwise a value. The caller classifies the three outcomes.
func term(i int) (uint64, error) {
	if i < 5 {
		return 0, errCompacted
	}
	if i > 9 {
		panic("index out of storage range")
	}
	return uint64(i) * 10, nil
}

func classifyTerm(i int) (kind string, v uint64) {
	defer func() {
		if p := recover(); p != nil {
			kind = "panic:" + p.(string)
		}
	}()
	v, err := term(i)
	if err == errCompacted {
		return "error:compacted", v
	}
	if err != nil {
		return "error:other", v
	}
	return "value", v
}

func main() {
	println(sentEntriesRecovered(1))
	println(classifyTerm(3))
	println(sentEntriesAbort())
}
