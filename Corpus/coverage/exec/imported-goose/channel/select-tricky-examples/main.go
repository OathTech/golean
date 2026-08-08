// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/channel/select_tricky_examples.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// Example with 2 nonblocking ops that should not match.
func select_nb_not_ready() {
	ch := make(chan struct{})
	go func() {
		select {
		case <-ch:
			panic("bad")
		default:
		}
	}()

	select {
	case ch <- struct{}{}:
		panic("bad")
	default:
	}
}

func select_nb_guaranteed_ready() {
	x := make(chan int)
	close(x)
	select {
	// non-blocking receive is guaranteed to execute
	case <-x:
	default:
		// must prove unreachable
		close(x)
	}
}

// Non-blocking send cannot send on a full buffer
func select_nb_full_buffer_not_ready() {
	// 1. Buffered channel of size 1
	ch := make(chan int, 1)

	// 2. Fill the buffer
	ch <- 0

	// 3. Nonblocking select:
	//    the send case would panic,
	//    so it must NOT be taken.
	select {
	case ch <- 0:
		panic("unreachable")
	default:
		// benign: correct behavior
	}
}

// --- GoLean harness ---
// Authored wrappers: each upstream example panics on a wrong select
// commitment; reaching the return (value 1) is the observable.

func goleanSelectNbNotReady() int {
	select_nb_not_ready()
	return 1
}

func goleanSelectNbGuaranteedReady() int {
	select_nb_guaranteed_ready()
	return 1
}

func goleanSelectNbFullBufferNotReady() int {
	select_nb_full_buffer_not_ready()
	return 1
}

func main() {}
