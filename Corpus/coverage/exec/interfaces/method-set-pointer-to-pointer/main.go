package main

// Go's method set of `*T` is defined only when `T` is a defined non-pointer,
// non-interface type: `**T` has an EMPTY method set (pre-merge audit
// 2026-07-31, finding 4 — the pointer auto-deref fallback fired for any
// `.pointer elem` and handed `**T` the methods of `*T`).

type ppIface interface{ M() int }

type ppT struct{ n int }

func (t *ppT) M() int { return t.n }

func pointerToPointerNoMethodSet() int {
	t := &ppT{n: 7}
	pp := &t
	var x any = pp
	_, ok := x.(ppIface)
	if ok {
		return 1
	}
	return 0
}

// The single-pointer control: `*T` DOES carry the pointer-receiver method.
func singlePointerMethodSet() int {
	t := &ppT{n: 7}
	var x any = t
	v, ok := x.(ppIface)
	if !ok {
		return 0
	}
	return v.M()
}
