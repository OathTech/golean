package main

import "fmt"

func maxCount(words []uint64) uint64 {
	counts := make(map[uint64]uint64)
	for i := 0; i < len(words); i++ {
		counts[words[i]]++
	}
	best := uint64(0)
	for _, c := range counts {
		if c > best {
			best = c
		}
	}
	return best
}

func maxCountFour(a, b, c, d uint64) uint64 {
	return maxCount([]uint64{a, b, c, d})
}

func maxCountOne(a uint64) uint64 {
	return maxCount([]uint64{a})
}

func maxCountEmpty() uint64 {
	return maxCount([]uint64{})
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", maxCountFour(7, 3, 7, 7))
}
