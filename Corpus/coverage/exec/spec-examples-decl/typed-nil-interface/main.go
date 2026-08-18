package main

// spec#Variables block Variables-1-60262a8d: an interface variable's
// DYNAMIC type is tracked separately from its static type — after x = v with
// v a nil *T, x holds value (*T)(nil) with dynamic type *T, so x != nil even
// though the stored pointer is nil.

type T struct{ n int }

func typedNilInterface() int {
	var x interface{} // x is nil and has static type interface{}
	var v *T          // v has value nil, static type *T
	n := 0
	if x == nil {
		n += 1
	}
	x = 42 // x has value 42 and dynamic type int
	if xi, ok := x.(int); ok && xi == 42 {
		n += 2
	}
	x = v // x has value (*T)(nil) and dynamic type *T
	if x != nil {
		n += 4 // the interface is NOT nil...
	}
	if pt, ok := x.(*T); ok && pt == nil {
		n += 8 // ...but the boxed pointer is
	}
	return n // 15
}
