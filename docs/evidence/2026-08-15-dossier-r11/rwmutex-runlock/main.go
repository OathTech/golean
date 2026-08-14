// R11 probe: RUnlock of an unlocked RWMutex — same fatal class.
package main

import "sync"

func main() {
	var m sync.RWMutex
	m.RUnlock()
	println("unreachable")
}
