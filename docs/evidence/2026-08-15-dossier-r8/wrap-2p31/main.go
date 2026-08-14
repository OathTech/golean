// R8 probe (misuse scale): a single Add(1<<31). The doc sentence only
// says "panics if the counter goes negative" — an unbounded-counter
// implementation would NOT panic here. gc keeps the counter in the
// high 32 bits of a uint64 and WRAPS before the negative test.
package main

import "sync"

func main() {
	defer func() {
		if r := recover(); r != nil {
			s, _ := r.(string)
			println("recovered:", s)
		} else {
			println("no panic: Add(1<<31) accepted")
		}
	}()
	var wg sync.WaitGroup
	wg.Add(1 << 31)
	println("after Add(1<<31): no panic")
}
