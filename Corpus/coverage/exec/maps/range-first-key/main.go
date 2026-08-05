package main

// The observable is GENUINELY map-iteration-order-dependent by design:
// the first key produced by `range` over a three-key map. Go randomizes
// iteration order per run, so `go run` explores the set {1, 2, 3} across
// repeated samples; the machine's admitted set is all three (one per
// choice of first pick). This is the membership lane's sampling-mode
// case (docs/2026-08-04_membership-lane-design.md): equality against a
// single `go run` is the wrong oracle here — membership of every Go
// sample in the machine-enumerated observation set is the right one.
func rangeFirstKey() int {
	m := map[int]int{1: 10, 2: 20, 3: 30}
	first := -1
	for k := range m {
		if first < 0 {
			first = k
		}
	}
	return first
}

func main() {
	rangeFirstKey()
}
