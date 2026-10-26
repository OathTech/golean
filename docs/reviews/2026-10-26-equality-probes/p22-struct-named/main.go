package main

func main() { run() }

type A struct{ X, Y int }
type B struct{ X, Y int }
type C A

type WithPtr struct{ P *int }
type WithIface struct{ I any }
type WithChan struct{ C chan int }
type WithArr struct{ A [2]int }
type WithStr struct{ S string }
type Deep struct {
	A A
	W WithArr
}

func run() {
	a := A{1, 2}
	println(a == A{1, 2}, a == A(B{1, 2}), a == A(C{1, 2}), B(a) == B{1, 2}, a != A{2, 1})
	println(any(a) == any(B{1, 2}), any(a) == any(A(B{1, 2})), any(a) == any(C(a)))
	x, y := 1, 1
	println(WithPtr{&x} == WithPtr{&x}, WithPtr{&x} == WithPtr{&y}, WithPtr{nil} == WithPtr{nil}, WithPtr{&x} == WithPtr{})
	println(WithIface{1} == WithIface{1}, WithIface{1} == WithIface{int64(1)}, WithIface{nil} == WithIface{}, WithIface{"a"} == WithIface{"a"}, WithIface{a} == WithIface{A{1, 2}})
	ch := make(chan int)
	println(WithChan{ch} == WithChan{ch}, WithChan{ch} == WithChan{make(chan int)}, WithChan{} == WithChan{nil})
	println(WithArr{[2]int{1, 2}} == WithArr{[2]int{1, 2}}, WithArr{[2]int{1, 2}} == WithArr{[2]int{1, 3}})
	println(WithStr{"a"} == WithStr{"a"}, WithStr{"a"} == WithStr{"b"}, WithStr{""} == WithStr{})
	d1 := Deep{A{1, 2}, WithArr{[2]int{3, 4}}}
	d2 := Deep{A{1, 2}, WithArr{[2]int{3, 4}}}
	println(d1 == d2, d1 == Deep{A{1, 2}, WithArr{[2]int{3, 5}}})
	m := map[A]int{}
	m[a] = 1
	m[A{1, 2}] = 2
	m[A(B{1, 2})] = 3
	m[A{2, 1}] = 4
	println(len(m), m[a])
	md := map[Deep]int{}
	md[d1] = 1
	md[d2] = 2
	println(len(md), md[d1])
	mi := map[WithIface]int{}
	mi[WithIface{1}] = 1
	mi[WithIface{int64(1)}] = 2
	mi[WithIface{1}] = 3
	println(len(mi), mi[WithIface{1}])
	var pa *A = &a
	println(*pa == a, *pa == A{1, 2})
	// pointer-to-struct fields vs value equality
	a2 := a
	println(a2 == a, &a2 == &a)
	// struct containing a pointer to a struct with same contents
	type Box struct{ P *A }
	println(Box{&a} == Box{&a}, Box{&a} == Box{&a2})
	// embedded struct equality
	type Emb struct {
		A
		Z int
	}
	println(Emb{A{1, 2}, 3} == Emb{A{1, 2}, 3}, Emb{A{1, 2}, 3} == Emb{A{1, 2}, 4})
	// switch on struct
	switch a {
	case A{0, 0}:
		println("zero")
	case A{1, 2}:
		println("one-two")
	}
}
