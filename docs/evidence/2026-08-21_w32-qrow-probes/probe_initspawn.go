// Q-INITSPAWN probe (2026-08-21, W3.2 slice 2 memo): does gc run an
// init-spawned goroutine DURING remaining init work, before main starts?
// The child sends on a buffered channel; init then burns registry-free
// work and polls with select+default BEFORE init returns. observed=1
// means the child executed while initialization code was still running
// (a during-init member); observed=0 means it had not run by the poll.
// Either way main also reports whether the child had run by main entry.
package main

import "fmt"

var ch = make(chan int, 1)
var observedInInit = -1

func init() {
	go func() { ch <- 1 }()
	sink := 0
	for i := 0; i < 200000000; i++ {
		sink += i & 3
	}
	_ = sink
	select {
	case v := <-ch:
		observedInInit = v
	default:
		observedInInit = 0
	}
}

func main() {
	byMain := 0
	if observedInInit == 1 {
		byMain = 1
	} else {
		select {
		case <-ch:
			byMain = 2 // ran only after init's poll
		default:
			byMain = 3 // still not run at main entry
		}
	}
	fmt.Println(observedInInit, byMain)
}
