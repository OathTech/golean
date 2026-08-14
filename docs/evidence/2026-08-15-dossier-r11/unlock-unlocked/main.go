// R11 probe: Unlock of an unlocked Mutex. DOCS say "run-time error";
// gc realizes an UNRECOVERABLE runtime throw — the deferred recover
// runs but cannot catch it (exit 2, fatal error line).
package main

import "sync"

func main() {
	defer func() {
		r := recover()
		println("deferred ran; recover() =", r == nil)
	}()
	var m sync.Mutex
	m.Unlock()
	println("unreachable")
}
