package main

// Two same-named local types in different functions; the cross-assert
// needs the OTHER function's type as an assert target, which only a
// closure declared in that scope can name.
func mkA() (any, func(any)) { type L int; return L(1), func(x any) { _ = x.(L) } }
func mkB() (any, func(any)) { type L int; return L(2), func(x any) { _ = x.(L) } }

func mkA2() (any, func(any)) {
	type L int
	return L(1), func(x any) { _ = x.(interface{ Get() L }) }
}
func mkB2() (any, func(any)) {
	type L int
	return L(1), func(x any) { _ = x.(interface{ Get() L }) }
}

func init() {
	va, _ := mkA()
	_, assertB := mkB()
	try("scopes: A-value asserted to B's L", func() { assertB(va) })
	va2, assertA2 := mkA2()
	_, assertB2 := mkB2()
	try("scopes: assert to own anon iface (missing)", func() { assertA2(va2) })
	try("scopes: assert to other anon iface (missing)", func() { assertB2(va2) })
}
