package main

// Multi-package guardrail (raft W1.1, 2026-08-18): the BUG-010
// collision witnesses. TWO source packages share the package NAME
// `inner` but live at DISTINCT import paths (`red/inner`, `blue/inner`),
// and each declares a type T and a func F; main declares its own
// dot-free T and F beside them. Go keys type identity on the import
// PATH (spec §Type identity: a defined type is identical only to
// itself; two same-named types from different packages are distinct),
// so every cross-assert below answers false and each F resolves to its
// own package's body. A package-NAME-keyed TypeId/FuncId (BUG-010)
// would fuse the inners: the asserts would answer true and the calls
// would be ambiguous.

import (
	bi "blue/inner"
	ri "red/inner"
)

type T struct {
	Tag int
}

func F() int {
	return 1
}

func sameNameTypeIdentity() int {
	var a any = ri.T{Tag: 1}
	got := 0
	if _, ok := a.(bi.T); ok { // red/inner.T is NOT blue/inner.T
		got += 1
	}
	if _, ok := a.(T); ok { // ... and NOT main.T
		got += 10
	}
	if v, ok := a.(ri.T); ok { // it IS red/inner.T
		got += 100 * v.Tag
	}
	var b any = T{Tag: 2}
	if _, ok := b.(ri.T); ok { // main.T is NOT red/inner.T
		got += 1000
	}
	if v, ok := b.(T); ok {
		got += 10000 * v.Tag
	}
	return got
}

func sameNameFuncIdentity() int {
	// Distinct FuncIds: main.F=1, red/inner.F=20, blue/inner.F=300.
	return F() + ri.F() + bi.F()
}

func main() {}
