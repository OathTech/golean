// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/struct_pointers.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type Bar struct {
	a uint64
	b uint64
}

// Foo contains a nested struct which is intended to be manipulated through a
// Foo pointer
type Foo struct {
	bar Bar
}

func (bar *Bar) mutate() {
	bar.a = 2
	bar.b = 3
}

func (foo *Foo) mutateBar() {
	foo.bar.mutate()
}

func testFooBarMutation() bool {
	x := Foo{bar: Bar{a: 0, b: 0}}
	x.mutateBar()
	return x.bar.a == 2
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestFooBarMutation() int {
	if testFooBarMutation() {
		return 1
	}
	return 0
}

func main() {}
