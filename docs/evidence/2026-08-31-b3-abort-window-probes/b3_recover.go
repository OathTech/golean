// B3 abort-window probe (RETURN-VALUE observable, no stdout needed).
// The deferred function recovers, so the program does NOT abort; the
// post-raise partner progress is then carried out in an ordinary RETURN
// VALUE -- i.e. it is inside the harness's observation channel, not the
// stderr-interleaving channel the G1 deferral argued was the only one.
package main

import "fmt"

func run() string {
	toMain := make(chan struct{})
	ack := make(chan string)
	out := make(chan string)

	go func() {
		defer func() {
			if r := recover(); r != nil {
				// Everything below is strictly after the raise.
				toMain <- struct{}{} // partner must be scheduled
				v := <-ack           // partner ran and replied
				out <- "raised=" + r.(string) + "; partner-after-raise=" + v
			}
		}()
		panic("boom")
	}()

	<-toMain
	ack <- "yes"
	return <-out
}

func main() {
	fmt.Println(run())
}
