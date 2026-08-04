package main

// Labeled continue and labeled break targeting a RANGE-over-map loop:
// the machine's mapIterK label paths. Observables are order-independent
// (sums), so the case is stable under the nondeterministic iteration
// pick.
func labeledBranchRangeMap() int {
	m := map[int]int{1: 10, 2: 20, 3: 30}
	contSum := 0
outer:
	for k, v := range m {
		for j := 0; j < 3; j++ {
			if j == 1 {
				continue outer
			}
			contSum += k + j
		}
		contSum += v * 100
	}
	breakSum := 0
loop:
	for k := range m {
		for j := 0; j < 2; j++ {
			breakSum += 1000
			if k > 0 {
				break loop
			}
		}
		breakSum = -1
	}
	return contSum*10 + breakSum
}

func main() {
	labeledBranchRangeMap()
}
