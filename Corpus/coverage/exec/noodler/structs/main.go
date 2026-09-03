// noodler probes — struct/array/pointer equality and value semantics
// (spec#Comparison_operators, spec#Struct_types, spec#Array_types).
package main

// An array containing NaN is not equal to itself.
func arrayWithNaNSelfEquality() (bool, bool) {
	zero := 0.0
	nan := zero / zero
	a := [2]float64{1, nan}
	b := [2]float64{1, 2}
	return a == a, b == b
}

// A struct with a NaN field is not equal to itself; != is true.
func structWithNaNField() (bool, bool) {
	type SN_struct struct {
		n int
		f float64
	}
	zero := 0.0
	s := SN_struct{1, zero / zero}
	return s == s, s != s
}

// Struct equality ignores nothing but compares all named fields.
func structEqualityAllFields() (bool, bool, bool) {
	type P_struct struct {
		x, y int
		s    string
	}
	a := P_struct{1, 2, "a"}
	b := P_struct{1, 2, "a"}
	c := P_struct{1, 2, "b"}
	return a == b, a == c, a != c
}

// Pointer equality: same variable, distinct variables, fields, elements.
func pointerEquality() (bool, bool, bool, bool) {
	x, y := 1, 1
	type SP_pointe struct{ a, b int }
	s := SP_pointe{}
	arr := []int{1, 2}
	sub := arr[1:]
	return &x == &x, &x == &y, &s.a == &s.b, &arr[1] == &sub[0]
}

// Pointers to struct copies differ; pointer to the same struct equal.
func pointerToCopies() (bool, bool) {
	type SC_pointe struct{ v int }
	a := SC_pointe{1}
	b := a
	p, q := &a, &a
	return &a == &b, p == q
}

// Arrays are values: assignment copies, and passing copies.
func arrayValueSemantics() (int, int) {
	a := [3]int{1, 2, 3}
	b := a
	b[0] = 99
	mod := func(x [3]int) int { x[1] = 77; return x[1] }
	r := mod(a)
	return a[0]*100 + a[1], b[0] + r
}

// Zero-length arrays compare equal; a struct of zero-length arrays too.
func zeroLengthArrayEquality() (bool, bool) {
	var a, b [0]int
	type E_zeroLe struct{ z [0]string }
	return a == b, E_zeroLe{} == E_zeroLe{}
}

// Nested struct equality with an inner array and pointer field.
func nestedStructEquality() (bool, bool) {
	type In_nested struct{ a [2]int }
	type Out_nested struct {
		in In_nested
		p  *int
	}
	x := 1
	o1 := Out_nested{In_nested{[2]int{1, 2}}, &x}
	o2 := Out_nested{In_nested{[2]int{1, 2}}, &x}
	o3 := Out_nested{In_nested{[2]int{1, 2}}, nil}
	return o1 == o2, o1 == o3
}

// Func values compare only to nil.
func funcNilComparison() (bool, bool) {
	var f func()
	g := func() {}
	return f == nil, g != nil
}

// Channel equality: same channel equal; nil channels equal each other.
func channelEquality() (bool, bool, bool) {
	a := make(chan int)
	b := a
	c := make(chan int)
	var n1, n2 chan int
	return a == b, a == c, n1 == n2
}

// Struct with a blank field: positional literal skips it? (not legal);
// blank fields are ignored in comparison — probe via zero values.
func structWithBlankField() (bool, int) {
	type B_struct struct {
		a int
		_ int
		b int
	}
	x := B_struct{a: 1, b: 2}
	y := B_struct{a: 1, b: 2}
	return x == y, x.a + x.b
}

// Struct copy on assignment: nested array inside is deep-copied.
func structCopyDeep() int {
	type SD_struct struct {
		arr [2]int
		sl  []int
	}
	a := SD_struct{[2]int{1, 2}, []int{1, 2}}
	b := a
	b.arr[0] = 9
	b.sl[0] = 9
	return a.arr[0]*10 + a.sl[0]
}

// Address of composite literal: distinct allocations, independent.
func addressOfCompositeLiteral() (int, bool) {
	type SA_addres struct{ v int }
	p := &SA_addres{1}
	q := &SA_addres{1}
	p.v = 5
	return p.v + q.v, p == q
}

// Comparing interfaces holding pointers to equal structs: pointer
// identity, not deep equality.
func interfacePointerIdentity() (bool, bool) {
	type SI_interf struct{ v int }
	a := &SI_interf{1}
	var x any = a
	var y any = a
	var z any = &SI_interf{1}
	return x == y, x == z
}

// Struct with embedded struct: equality includes the embedded fields.
func embeddedStructEquality() (bool, bool) {
	type In_embedd struct{ n int }
	type Out_embedd struct {
		In_embedd
		s string
	}
	a := Out_embedd{In_embedd{1}, "x"}
	b := Out_embedd{In_embedd{1}, "x"}
	c := Out_embedd{In_embedd{2}, "x"}
	return a == b, a == c
}

// Array of structs equality and element assignment.
func arrayOfStructs() (bool, int) {
	type P_arrayO struct{ x, y int }
	a := [2]P_arrayO{{1, 2}, {3, 4}}
	b := a
	b[1].y = 40
	return a == b, a[1].y + b[1].y
}

// Multi-dimensional arrays: value copy and indexing.
func multiDimArrays() (int, int) {
	var g [2][3]int
	for i := 0; i < 2; i++ {
		for j := 0; j < 3; j++ {
			g[i][j] = i*10 + j
		}
	}
	h := g
	h[1][2] = 99
	row := g[1]
	row[0] = 77
	return g[1][2] + g[1][0], h[1][2] + len(row)
}

// Slice of arrays: element arrays are values inside the slice.
func sliceOfArrays() int {
	s := [][2]int{{1, 2}, {3, 4}}
	a := s[0]
	a[0] = 9
	s[1][0] = 8
	return s[0][0]*100 + s[1][0]*10 + a[0]
}

// Pointer to array: indexing and range through the pointer alias.
func pointerToArrayAlias() (int, int) {
	a := [3]int{1, 2, 3}
	p := &a
	p[0] = 10
	sum := 0
	for _, v := range p {
		sum += v
	}
	return a[0], sum
}

// Recursive type: a linked list built and summed.
type node struct {
	v    int
	next *node
}

func linkedListSum() int {
	var head *node
	for i := 1; i <= 5; i++ {
		head = &node{i, head}
	}
	sum := 0
	for n := head; n != nil; n = n.next {
		sum = sum*10 + n.v
	}
	return sum
}

// Struct field of function type invoked through the struct.
func structFuncField() int {
	type Op_struct struct {
		name string
		fn   func(int, int) int
	}
	ops := []Op_struct{{"add", func(a, b int) int { return a + b }}, {"mul", func(a, b int) int { return a * b }}}
	return ops[0].fn(2, 3)*10 + ops[1].fn(2, 3)
}

func main() {}
