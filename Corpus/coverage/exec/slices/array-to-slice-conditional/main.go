package main

import "fmt"

// fillFromRight mirrors quorum.CommittedIndex's on-stack-else-heap slice
// selection and right-to-left fill.
func fillFromRight(n int) uint64 {
	var stk [7]uint64
	var srt []uint64
	if len(stk) >= n {
		srt = stk[:n]
	} else {
		srt = make([]uint64, n)
	}
	i := n - 1
	for j := 0; j < n; j++ {
		srt[i] = uint64(j + 1)
		i--
	}
	var sum uint64
	for k := 0; k < len(srt); k++ {
		sum += srt[k]
	}
	return sum
}

func arrayToSliceConditional() int {
	// n=5 takes the on-stack branch (5 <= 7); n=9 takes the make branch.
	return int(fillFromRight(5) + fillFromRight(9))
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", arrayToSliceConditional())
}
