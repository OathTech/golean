package main

func main() { run() }

type B struct {
	_ int
	X int
	_ string
}

type Padded struct {
	A int8
	B int64
	C int8
}

type Nested struct {
	In B
	Y  int
}

func run() {
	a := B{1, 7, "p"}
	b := B{2, 7, "q"}
	c := B{2, 8, "q"}
	println(a == b, a != b, a == c, b == c)
	m := map[B]int{}
	m[a] = 1
	m[b] = 2
	m[c] = 3
	println(len(m), m[B{9, 7, "z"}], m[B{0, 8, ""}])
	var i, j any = a, b
	println(i == j, i == any(c))
	arr1 := [1]B{a}
	arr2 := [1]B{b}
	println(arr1 == arr2)
	n1 := Nested{a, 1}
	n2 := Nested{b, 1}
	println(n1 == n2, n1 == Nested{c, 1})
	p := Padded{1, 2, 3}
	q := Padded{1, 2, 3}
	println(p == q, p != Padded{1, 2, 4})
	mp := map[Padded]int{p: 1}
	mp[q] = 2
	println(len(mp), mp[Padded{1, 2, 3}])
	e1 := struct{}{}
	e2 := struct{}{}
	println(e1 == e2)
	type Empty struct{}
	me := map[Empty]int{}
	me[Empty{}] = 1
	me[Empty{}] = 2
	println(len(me), me[Empty{}])
	switch n1 {
	case Nested{c, 1}:
		println("c")
	case Nested{b, 1}:
		println("b")
	}
}
