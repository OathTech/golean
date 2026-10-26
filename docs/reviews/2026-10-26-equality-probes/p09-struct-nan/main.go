package main

func main() { run() }

type S struct {
	F float64
	N int
}

func run() {
	zero := 0.0
	nan := zero / zero
	s1 := S{nan, 1}
	s2 := S{nan, 1}
	println(s1 == s2, s1 != s2, s1 == s1)
	z1 := S{zero, 1}
	z2 := S{-zero, 1}
	println(z1 == z2, z1 != z2)
	a1 := [2]float64{nan, 1}
	a2 := [2]float64{nan, 1}
	println(a1 == a2, a1 != a2, [2]float64{zero, 1} == [2]float64{-zero, 1})
	var i1, i2 any = s1, s2
	println(i1 == i2, i1 != i2)
	var j1, j2 any = nan, nan
	println(j1 == j2, j1 != j2, j1 == j1)
	var k1, k2 any = zero, -zero
	println(k1 == k2)
	m := map[S]int{}
	m[s1] = 1
	m[s2] = 2
	m[z1] = 3
	m[z2] = 4
	println(len(m), m[S{0, 1}], m[S{nan, 1}])
	switch s1 {
	case s2:
		println("matched nan struct")
	default:
		println("no match")
	}
	switch z1 {
	case z2:
		println("matched negz struct")
	default:
		println("no match")
	}
	// nested: struct holding an array of structs with NaN
	type T struct{ A [1]S }
	t1 := T{[1]S{{nan, 0}}}
	println(t1 == t1, t1 == T{[1]S{{zero, 0}}})
	// interface holding array with NaN
	var x1, x2 any = a1, a2
	println(x1 == x2)
	mm := map[any]int{}
	mm[j1] = 1
	mm[j2] = 2
	mm[k1] = 3
	mm[k2] = 4
	println(len(mm), mm[k1], mm[0.0], mm[j1])
	for k, v := range mm {
		if f, ok := k.(float64); ok && f == 0 {
			println("iface zero key sign", 1/f > 0, v)
		}
	}
}
