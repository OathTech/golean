package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: `make` with a
// RUN-TIME negative size at the kinds and shapes BUG-081's rows (the
// allocation limit) and noodler/bounds/make-negative-len (`int` len) do not
// pin — a negative cap, a negative len of int64 and int8 kind, a negative
// channel size of int64 kind, the recover route; and the MAP control: the
// spec's clause (#Making_slices_maps_and_channels) names slices and channels,
// and gc's makemap clamps a negative hint to zero — NO panic.

func makeSliceNegativeCap(z int) int {
	s := make([]int, 0, z)
	return cap(s)
}

func makeSliceLenInt64Negative(z int) int {
	n := int64(z)
	s := make([]int, n)
	return len(s)
}

func makeSliceLenInt8Negative(z int) int {
	n := int8(z)
	s := make([]int, n)
	return len(s)
}

func makeChanSizeInt64Negative(z int) int {
	n := int64(z)
	c := make(chan int, n)
	return cap(c)
}

func makeMapNegativeHint(z int) int {
	m := make(map[int]int, z)
	m[1] = 1
	return len(m)
}

func makeMapHintInt64Negative(z int) int {
	n := int64(z)
	m := make(map[int]int, n)
	m[1] = 1
	return len(m) + 10
}

func makeSliceNegativeLenRecovered(z int) int {
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		s := make([]int, z)
		r = len(s)
	}()
	return r + 1
}

func main() {}
