// B3 abort-window probe (SHARP: separates .panicking from .panicked).
//
// The model distinguishes `.panicking` (mid-unwind, still steppable, other
// goroutines may run) from `.panicked` (fully unwound, unrecovered) --
// execProgLoop aborts on EVERY stream the instant any thread is `.panicked`
// (Multi.lean:1618). So the question that actually bites B3 is:
//
//   does a partner goroutine make progress AFTER the panicking goroutine
//   is fully unwound and unrecoverable?
//
// The runtime's own "panic: boom" traceback on stderr is emitted by
// fatalpanic, which runs strictly AFTER the goroutine is unrecoverable.
// Merging stdout and stderr onto one fd (2>&1, both unbuffered write(2))
// therefore gives an ordering: any "B" line AFTER the "panic:" line is
// partner progress strictly after the model's abort point.
package main

import (
	"fmt"
	"os"
)

func main() {
	go func() {
		defer fmt.Fprintln(os.Stdout, "A-last-defer (still .panicking)")
		panic("boom")
	}()
	for i := 0; ; i++ {
		fmt.Fprintln(os.Stdout, "B", i)
	}
}
