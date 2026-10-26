package main

func main() { run() }

type P struct{ X, Y int }

func run() {
	println([2]int{1, 2} == [2]int{1, 2}, [2]int{1, 2} != [2]int{2, 1}, [0]int{} == [0]int{})
	println([2][2]int{{1, 2}, {3, 4}} == [2][2]int{{1, 2}, {3, 4}}, [2][2]int{{1, 2}, {3, 4}} == [2][2]int{{1, 2}, {3, 5}})
	println([2]string{"a", "b"} == [2]string{"a", "b"}, [2]string{"a", "b"} != [2]string{"a", "c"})
	x, y := 1, 1
	println([2]*int{&x, &y} == [2]*int{&x, &y}, [2]*int{&x, &y} == [2]*int{&y, &x}, [1]*int{&x} == [1]*int{nil})
	println([2]P{{1, 2}, {3, 4}} == [2]P{{1, 2}, {3, 4}}, [2]P{{1, 2}, {3, 4}} == [2]P{{1, 2}, {4, 3}})
	m := map[[2]int]int{}
	m[[2]int{1, 2}] = 1
	m[[2]int{1, 2}] = 2
	m[[2]int{2, 1}] = 3
	println(len(m), m[[2]int{1, 2}], m[[2]int{2, 1}], m[[2]int{}])
	mm := map[[2][2]int]string{}
	mm[[2][2]int{{1, 2}, {3, 4}}] = "a"
	mm[[2][2]int{{1, 2}, {3, 4}}] = "b"
	println(len(mm), mm[[2][2]int{{1, 2}, {3, 4}}])
	type Arr [2]int
	var a Arr = Arr{1, 2}
	println(a == Arr{1, 2}, a == [2]int{1, 2}, Arr([2]int{1, 2}) == a, any(a) == any([2]int{1, 2}), any(a) == any(Arr{1, 2}))
	var ia, ib any = [2]int{1, 2}, [2]int{1, 2}
	println(ia == ib)
	ma := map[any]int{}
	ma[[2]int{1, 2}] = 1
	ma[Arr{1, 2}] = 2
	ma[[2]int{1, 2}] = 3
	println(len(ma), ma[[2]int{1, 2}], ma[Arr{1, 2}])
	arr := [3]int{1, 2, 3}
	brr := arr
	brr[0] = 9
	println(arr == brr, arr == [3]int{1, 2, 3})
	pa := &arr
	println(*pa == arr, *pa == [3]int{1, 2, 3})
	// array of arrays of bools and bytes
	println([2]byte{1, 2} == [2]byte{1, 2}, [2]bool{true, false} == [2]bool{true, false})
	// big array
	var big1, big2 [100]int
	big2[99] = 1
	println(big1 == big2, big1 == [100]int{})
	switch arr {
	case [3]int{1, 2, 3}:
		println("switch array matched")
	}
}
