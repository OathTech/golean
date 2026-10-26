package main

func main() { run() }

type P *int

type T struct{ A, B int }

var g int
var gs T

func fresh() *int {
	y := 0
	return &y
}

func run() {
	x := 1
	var pp P = &x
	println(pp == &x, (*int)(pp) == &x, &x == &x, any(pp) == any(&x), any((*int)(pp)) == any(&x))
	println(fresh() == fresh(), new(int) == new(int), &g == &g, &gs.A == &gs.A, &gs.A == &gs.B)
	a := fresh()
	b := a
	println(a == b, *a == *b)
	arr := [3]int{1, 2, 3}
	println(&arr[1] == &arr[1], &arr[0] == &arr[1], &arr == &arr, &arr[0] == &arr[0])
	sl := arr[:]
	println(&sl[1] == &arr[1], &sl[0] == &arr[0], &sl[2] == &arr[2])
	t1 := T{1, 2}
	t2 := T{1, 2}
	println(&t1 == &t2, t1 == t2, &t1.A == &t1.A, &t1.A == &t2.A)
	pt := &t1
	println(&pt.A == &t1.A, &(*pt).B == &t1.B, pt == &t1)
	pz1 := new(struct{})
	pz2 := new(struct{})
	println("zero-size pointers (latitude):", pz1 == pz2)
	var z1, z2 [0]int
	println("zero-size arrays (latitude):", &z1 == &z2)
	m := map[*int]int{}
	m[&x] = 1
	m[pp] = 2
	m[a] = 3
	println(len(m), m[&x], m[a], m[fresh()])
	mp := map[P]int{}
	mp[pp] = 1
	mp[&x] = 2
	println(len(mp), mp[pp])
	// pointer to pointer identity
	ppx := &pp
	println(*ppx == &x, ppx == &pp)
	// closure-captured variable identity
	c := 0
	f1 := func() *int { return &c }
	f2 := func() *int { return &c }
	println(f1() == f2(), f1() == &c)
	// method value receiver identity
	switch &x {
	case pp:
		println("switch ptr matched named ptr")
	default:
		println("switch default")
	}
}
