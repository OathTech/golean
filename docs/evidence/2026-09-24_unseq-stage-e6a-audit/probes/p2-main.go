package main

// Audit probes — Stage E6a attack 2: len/cap over map / channel operands.

func wit(x int) int { println("wit", x); return x }

func lenNilMap() int {
	var m map[int]int
	return wit(1) + len(m)
}

func lenNilChan() int {
	var ch chan int
	return wit(1) + len(ch) + cap(ch)
}

func capChanBuffered() int {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	return wit(1) + len(ch)*10 + cap(ch)
}

func add(m map[int]int) int { m[7] = 7; return 10 }

func lenMapVsMutator() int { // len before add: 1 + 10
	m := map[int]int{1: 1}
	return len(m) + add(m)
}

func mutatorVsLenMap() int { // add before len: 10 + 2
	m := map[int]int{1: 1}
	return add(m) + len(m)
}

func lenMapReassign() int { // m captured and REASSIGNED by the sibling: m's read inside len's window, before reset
	m := map[int]int{1: 1}
	reset := func() int { m = map[int]int{1: 1, 2: 2, 3: 3}; return 10 }
	return len(m) + reset()
}

func sendOne(ch chan int) int { ch <- 1; return 100 }

func lenChanVsSend() int { // len before the send: 0 + 100
	ch := make(chan int, 2)
	return len(ch) + sendOne(ch)
}

func sendVsLenChan() int { // send before len: 100 + 1
	ch := make(chan int, 2)
	return sendOne(ch) + len(ch)
}

func assertVsLenMapIdx() int { // the assertion vs t[k] inside len(mm[...])'s window — E6a's widening on a map read
	var iv interface{} = "s"
	mm := map[int]map[int]int{1: {1: 1}}
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(mm[t[k]])
}

func lenMapMissingInner() int { // len of a nil inner map = 0
	mm := map[int]map[int]int{}
	return wit(2) + len(mm[3])
}

func lenMapVsIdx() int { // a map read (cannot fail) vs an index panic and a call: the set has the call before/after s[i]
	m := map[int]int{1: 1}
	s := []int{1}
	i := 9
	return len(m) + s[i] + wit(5)
}

func capChanVsCall() int {
	ch := make(chan int, 4)
	grow := func() int { ch = make(chan int, 8); return 1 }
	return cap(ch) + grow()
}

func main() {}
