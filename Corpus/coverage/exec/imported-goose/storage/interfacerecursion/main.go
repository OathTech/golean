// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/interfacerecursion/x.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type A interface {
	Foo()
}

type B interface {
	Bar()
}

type c struct { // ERROR cycle in dependencies
}

func (c *c) Foo() {
	var y B = c
	y.Bar()
}

func (c *c) Bar() {
	var y A = c
	y.Foo()
}

// --- GoLean harness ---
// Authored wrapper: constructs the type whose METHODS are mutually
// recursive through two interfaces (goose REJECTS this package with
// "// ERROR cycle in dependencies"; it is valid Go). The methods are
// deliberately not called (calling either diverges by construction);
// the observable is that lowering + interface assignment work.

func goleanInterfaceRecursion() int {
	v := &c{}
	var a A = v
	var b B = v
	_ = a
	_ = b
	return 1
}

func main() {}
