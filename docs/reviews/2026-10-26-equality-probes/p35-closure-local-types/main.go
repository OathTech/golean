package main

func main() { run() }

func run() {
	mk1 := func() any {
		type T struct{ X int }
		return T{1}
	}
	mk2 := func() any {
		type T struct{ X int }
		return T{1}
	}
	println(mk1() == mk1(), mk1() == mk2(), mk2() == mk2())
	m := map[any]int{}
	m[mk1()] = 1
	m[mk2()] = 2
	m[mk1()] = 3
	println(len(m), m[mk1()], m[mk2()])
	outer := func() (any, any) {
		type T struct{ X int }
		inner := func() any {
			type T struct{ X int }
			return T{1}
		}
		return T{1}, inner()
	}
	o, i := outer()
	println(o == i, o == o, i == i)
}
