package main

import "fmt"

type T int

func (T) Get() int { return 1 }
func (T) get() int { return 1 }

type U int

type S struct{ X int }

func (S) A()     {}
func (S) B() int { return 0 }

func try(name string, f func()) {
	defer func() { fmt.Printf("%s: %v\n", name, recover()) }()
	f()
}

func localA() any { type L int; return L(1) }
func localB() any { type L int; return L(2) }
func localIface() any {
	type L int
	var a any = L(1)
	return a
}

func main() {
	var a any = T(1)
	try("named->named", func() { _ = a.(U) })
	try("named->anon-missing", func() { _ = a.(interface{ M() }) })
	try("named->anon-two", func() { _ = a.(interface{ Get() int; M() }) })
	try("named->anon-order", func() { _ = a.(interface{ Z(); A() }) })
	try("anon-src->named", func() { var s interface{ Get() int } = T(1); _ = s.(V) })
	try("anon-src-two->named", func() { var s interface{ Get() int; get() int } = T(1); _ = s.(V) })
	try("anon-with-named-result", func() { _ = a.(interface{ Get() T }) })
	try("anon-with-embedded", func() { _ = a.(interface{ error; Get() int }) })
	try("anon-unexported", func() { _ = a.(interface{ get() int; M() }) })
	try("nil->anon", func() { var n any; _ = n.(interface{ M() }) })
	try("nil->named-iface", func() { var n any; _ = n.(fmt.Stringer) })
	try("nil->concrete", func() { var n any; _ = n.(T) })
	try("struct->anon-struct", func() { var s any = S{1}; _ = s.(struct{ X int }) })
	try("anon-struct-src", func() { var s any = struct{ X int }{1}; _ = s.(S) })
	try("func", func() { _ = a.(func(int) bool) })
	try("ptr", func() { _ = a.(*T) })
	try("slice-of-anon", func() { _ = a.([]interface{ M() }) })
	try("map-of-anon", func() { _ = a.(map[string]interface{ M() }) })
	try("chan", func() { _ = a.(chan T) })
	try("local->local", func() { la := localA(); _ = la.(U) })
	try("localA->localB-type", func() {
		la := localA()
		lb := localB()
		fmt.Printf("  eq=%v %T %T\n", la == lb, la, lb)
		// assert la to B's L: need B's type; via a type switch on lb's type is impossible; use helper below
	})
	try("local->anon-missing", func() { la := localA(); _ = la.(interface{ M() }) })
	try("uncomparable", func() { var x any = []int{1}; var y any = []int{1}; _ = x == y })
	try("uncomparable-anon-struct", func() { var x any = struct{ F []int }{}; var y any = struct{ F []int }{}; _ = x == y })
	try("local-in-anon-iface", func() {
		type L int
		var s any = T(1)
		_ = s.(interface{ Get() L })
	})
	fmt.Printf("%%T local: %T; %%v: %v\n", localA(), localA())
	fmt.Printf("%%T anon iface var: %T\n", func() interface{ Get() int } { return T(1) }())
}

type V int

func (V) Get() int { return 2 }
func (V) get() int { return 2 }
