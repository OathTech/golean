package main

func main() { run() }

type MyInt int
type MyStr string
type Alias = int

func run() {
	println(any(1) == any(int64(1)), any(1) == 1, 1 == any(1), any("a") == "a", "a" == any("a"))
	println(any(1.0) == any(1), any(uint8(1)) == any(byte(1)), any(int32(1)) == any(rune(1)), any(MyInt(1)) == any(1), any(Alias(1)) == any(1))
	println(any(MyInt(1)) == MyInt(1), any(MyStr("a")) == any("a"), any(MyStr("a")) == MyStr("a"))
	var i any = 3
	println(i == 3, i == int64(3), i != 3, i == 3.0, i == "3", i == true)
	var j any = int64(3)
	println(j == 3, j == int64(3), j == i)
	var s any = "x"
	switch s {
	case 1:
		println("one")
	case "x":
		println("x")
	default:
		println("def")
	}
	var mi any = MyInt(5)
	switch mi {
	case 5:
		println("plain 5")
	case MyInt(5):
		println("MyInt 5")
	}
	x := 5
	switch x {
	case mi:
		println("tag int, case iface MyInt matched")
	default:
		println("tag int, case iface MyInt default")
	}
	var pi any = 5
	switch x {
	case pi:
		println("tag int, case iface int matched")
	default:
		println("tag int, case iface int default")
	}
	var a [2]int = [2]int{1, 2}
	var ai any = a
	println(ai == any([2]int{1, 2}), ai == a, ai == any([2]int64{1, 2}))
	type S struct{ A, B int }
	var si any = S{1, 2}
	println(si == any(S{1, 2}), si == S{1, 2}, si == any(S{2, 1}))
	var pa any = &a
	println(pa == any(&a), pa == &a, pa == any(&a[0]))
	var e1 error
	var e2 any
	println(e1 == nil && e2 == nil, any(e1) == e2)
	var fs any = float32(1)
	var fd any = float64(1)
	println(fs == fd, fs == any(float32(1)))
}
