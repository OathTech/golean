// Deliberately racy: two goroutines write x unsynchronized; under
// -race the detector reports and the process exits with the TSan
// default exit code.
package main

import "time"

var x int

func main() {
	go func() { x = 1 }()
	x = 2
	time.Sleep(100 * time.Millisecond)
	println("done", x)
}
