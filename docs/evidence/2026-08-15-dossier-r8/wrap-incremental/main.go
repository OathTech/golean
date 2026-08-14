// R8 probe (misuse scale): reach 2^31 in two positive steps.
// Unbounded semantics: fine. 32-bit wrap-before-test: panic.
package main

import "sync"

func main() {
	defer func() {
		if r := recover(); r != nil {
			s, _ := r.(string)
			println("recovered:", s)
		} else {
			println("no panic")
		}
	}()
	var wg sync.WaitGroup
	wg.Add(1<<31 - 1)
	println("after Add(2^31-1): ok")
	wg.Add(1)
	println("after +1: no panic")
}
