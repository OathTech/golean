package main

import "sync"

// PERMANENT-until-lifted refusal marker (design note §9, D4:
// sync.Cond is OUT of slice-2 scope): a Signal with no waiter is a
// no-op, so the go side runs clean — the case is red at
// frontend-export by design until a Cond slice lifts it.
func condSignalNoWaiter() int {
	var m sync.Mutex
	c := sync.NewCond(&m)
	c.Signal()
	return 1
}

func main() {
	condSignalNoWaiter()
}
