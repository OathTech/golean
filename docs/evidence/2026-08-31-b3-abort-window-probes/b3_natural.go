// B3 abort-window probe (natural / unsynchronized).
// Worker runs `defer <print A>` then panics. Main spins printing B.
// Question: does any "B" appear on stdout AFTER "A"?
// "A" is definitionally post-raise (a deferred call runs only after the
// panic is raised). A "B" after it is post-raise PARTNER progress.
package main

import (
	"fmt"
	"os"
	"time"
)

func worker() {
	defer fmt.Fprintln(os.Stdout, "A")
	panic("boom")
}

func main() {
	go func() {
		time.Sleep(2 * time.Millisecond)
		worker()
	}()
	for i := 0; i < 2000000; i++ {
		fmt.Fprintln(os.Stdout, "B", i)
	}
}
