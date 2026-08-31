// B3 abort-window probe (deterministic / forced handshake).
// The panicking goroutine's DEFERRED function (post-raise by definition)
// hands off to main and waits for main's acknowledgement.
// If main's "B" is printed and the deferred func observes the ack, the gc
// runtime demonstrably schedules a partner goroutine to completion of a
// full communication round trip STRICTLY AFTER the panic is raised.
package main

import (
	"fmt"
	"os"
)

var toMain = make(chan struct{})
var ack = make(chan struct{})

func worker() {
	defer func() {
		fmt.Fprintln(os.Stdout, "A (deferred, post-raise)")
		toMain <- struct{}{} // partner must run to receive this
		<-ack                // partner must run again to send this
		fmt.Fprintln(os.Stdout, "C (deferred, after partner round trip)")
	}()
	panic("boom")
}

func main() {
	go worker()
	<-toMain
	fmt.Fprintln(os.Stdout, "B (main, strictly after A)")
	ack <- struct{}{}
	select {} // park main; let the panic finish unwinding
}
