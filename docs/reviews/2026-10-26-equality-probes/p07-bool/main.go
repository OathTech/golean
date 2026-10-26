package main

func main() { run() }

func run() {
	t := 1 < 2
	f := 2 < 1
	println(t == true, f == false, t == f, t != f, !t == f, (t && f) == false, (t || f) == true)
	switch t {
	case false:
		println("false")
	case true:
		println("true")
	}
	switch {
	case f:
		println("f")
	case t:
		println("t")
	}
	var a any = t
	var b any = true
	println(a == b, a == true, a != false, a == 1)
	type MyBool bool
	var mb MyBool = true
	println(mb == true, mb != false, bool(mb) == t, any(mb) == any(true), any(mb) == any(MyBool(true)))
	m := map[bool]int{true: 1}
	m[1 < 2] = 2
	println(len(m), m[true], m[false])
	arr := [2]bool{true, false}
	println(arr == [2]bool{true, false}, arr != [2]bool{false, true})
}
