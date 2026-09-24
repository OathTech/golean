package main

// Audit probes — sizing the class: a LATE failing operand (index / deref / division) left of an inline built-in
// participant (len / cap / min / max) whose own operand panics — call-free.

func idxVsMin() int {
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + min(t[k], 1)
}

func idxVsMax() int {
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + max(t[k], 1)
}

func idxVsCapSlice() int {
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + cap(t[k:])
}

func derefVsLenStr() int {
	var p *int
	str := "ab"
	i := 9
	return *p + len(str[i:])
}

func idxVsLenMapIdx() int { // the map-read window: len(mm[t[k]]) — E6a's len-over-map widening
	s := []int{1}
	mm := map[int]map[int]int{}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + len(mm[t[k]])
}

func compoundVsMin() int {
	x := make([]int, 1)
	t := []int{1, 2}
	k := 5
	x[9] += min(t[k], 1)
	return x[0]
}

func idxVsLenNested() int { // s[i] + len(b[j][0:]) — a nested failing chain inside len's window
	s := []int{1}
	b := [][]int{{1}}
	i, j := 9, 5
	return s[i] + len(b[j][0:])
}

func idxVsLenRightIdx() int { // the mirror: len(b[j]) + s[i]
	s := []int{1}
	b := [][]int{{1}}
	i, j := 9, 5
	return len(b[j]) + s[i]
}

func main() {}
