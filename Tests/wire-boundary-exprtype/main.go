package main

// The `type`-key wire-boundary fixture (release-readiness punch list item 2,
// 2026-10-12): `probe` answers 42 through the two decoder consumers of an
// expression node's `type` key — a blank assignment's discard temporary
// (`_ = n + 1`: the rhs node types `$blank0`) and a range's collection
// temporary (`for range s`: the collection node types `$rcoll`). The
// controls delete the `type` key from each node's BYTES and must refuse
// through the real CLI naming the node kind and its position
// (GoLean/NativeToIR.lean `exprTypeOf` — which, before, declared the
// temporary `int` whatever value it held).

func probe() int {
	n := 0
	_ = n + 1
	s := []int{1, 2, 3}
	for range s {
		n++
	}
	return n + 39
}

func main() { println(probe()) }
