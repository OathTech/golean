package main

func gAssertVsPlainCall() int {
	var iv any = "s"
	return iv.(int) + boom()
}

func gAssertVsHintCall() int {
	var iv any = "s"
	return iv.(int) + len(make(map[int]int, boom()))
}

func gAssertVsSliceMakeLen() int {
	var iv any = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(make([]int, t[k]))
}

func gAssertVsChanMakeCap() int {
	var iv any = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + cap(make(chan int, t[k]))
}

func gAssertVsNewCall() int {
	var iv any = "s"
	return iv.(int) + *new(int) + zero()
}

func gAssertVsMapIndexHint() int {
	var iv any = "s"
	var nm map[int]int
	return iv.(int) + len(make(map[int]int, nm[1]))
}

func gAssertVsHintPlainVar() int {
	var iv any = "s"
	n := 2
	return iv.(int) + len(make(map[int]int, n))
}

func boom() int { panic("boom-call") }
func zero() int { return 0 }
