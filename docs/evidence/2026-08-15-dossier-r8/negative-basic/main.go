// R8 probe: the documented misuse — counter goes negative.
// Also witnesses the panic VALUE class: a plain string (recover
// asserts .(string)), not a runtime.Error.
package main

import "sync"

func main() {
	defer func() {
		if r := recover(); r != nil {
			s, isString := r.(string)
			println("recovered (string?", isString, "):", s)
		}
	}()
	var wg sync.WaitGroup
	wg.Add(-1)
}
