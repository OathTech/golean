package main

// RED PIN (arc-final audit F11, with F10's trigger-scope correction):
// select-with-select rendezvous is refused fail-closed
// ("select-with-select rendezvous (unmodeled this slice)",
// selectArrivalCases, Multi.lean) — a capability goose/perennial DO
// model and test (their blocking TrySend/TryReceive offer protocol;
// TestSelfSelect). The refusal's TRUE trigger is broader than the
// completion record's "both sides parked selects" phrasing (F10): it
// fires whenever ANY ready-or-waiter-carrying clause of an ARRIVING
// select has a parked-select partner — even when a DIFFERENT clause is
// cell-ready and could commit with no select-to-select pairing (the
// common worker idiom: a select polling several channels where one
// partner happens to be a select loop). Both shapes are pinned red
// here until the rendezvous (or the per-clause refusal narrowing)
// lands. Owner: recorded in the completion record's standing-red set
// and the goose-perennial matrix S2 row.

// The core gap: two blocking selects must rendezvous.
func selectToSelect() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		select {
		case ch <- 9:
			done <- 1
		}
	}()
	v := 0
	select {
	case v = <-ch:
	}
	<-done
	return v // 9
}

// F10's over-refusal shape: clause 0 (buffered, holding 5) is
// cell-ready and needs no pairing, but clause 1's only partner is a
// parked select — the arrival refuses the WHOLE select rather than
// only the select-partnered clause.
func selectBesideSelectLoop() int {
	buf := make(chan int, 1)
	buf <- 5
	un := make(chan int)
	go func() {
		select {
		case un <- 9:
		}
	}()
	v := 0
	select {
	case v = <-buf:
	case w := <-un:
		v = w * 10
	}
	return v // 5 or 90 in gc; refused on every schedule where the
	// partner has parked (the default stream commits 5 before the
	// partner parks, so this pin sits red at stage nondet: the
	// adversarial streams hit the refusal)
}

func main() {
	selectToSelect()
	selectBesideSelectLoop()
}
