// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/channel/actris_example.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// prog3 from Actris 2.0 intro: https://arxiv.org/pdf/2010.15030
func DSPExample() int {
	c, signal := make(chan any), make(chan any)

	go func() {
		ptr := (<-c).(*int)
		*ptr = *ptr + 2
		signal <- struct{}{}
	}()

	ptr := new(40)
	c <- ptr
	<-signal
	return *ptr // dereference to get 42
}

// --- GoLean harness ---
// Authored wrapper: the Actris prog3 rendezvous returns 42.

func goleanDSPExample() int {
	return DSPExample()
}

func main() {}
