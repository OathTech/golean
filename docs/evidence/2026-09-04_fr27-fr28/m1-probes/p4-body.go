package main

func fLeftIndexVsHintIndex() int {
	s := []int{1}
	t := []int{1, 2}
	i := 9
	k := 5
	return s[i] + len(make(map[int]int, t[k]))
}

func fLeftDivVsHintIndex() int {
	z := 0
	t := []int{1, 2}
	k := 5
	return 1/z + len(make(map[int]int, t[k]))
}

func fLeftAssertVsHintIndex() int {
	var iv any = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(make(map[int]int, t[k]))
}

func fHintIndexVsRightIndex() int {
	s := []int{1}
	t := []int{1, 2}
	i := 9
	k := 5
	return len(make(map[int]int, t[k])) + s[i]
}

func fLeftNilDerefVsHintIndex() int {
	var p *int
	t := []int{1, 2}
	k := 5
	return *p + len(make(map[int]int, t[k]))
}

func fLeftIndexHintCallPanic() int {
	s := []int{1}
	i := 9
	return s[i] + len(make(map[int]int, boom()))
}

func boom() int { panic("boom-call") }
