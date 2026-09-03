// noodler probes — resource envelopes: deep (non-tail) recursion and
// long loops that gc runs trivially. A machine refusal here is an
// exhausted-budget refusal (charter: named at the point of failure).
package main

func depth(n int) int {
	if n == 0 {
		return 0
	}
	return 1 + depth(n-1)
}

func recursionDepth(n int) int { return depth(n) }

func loopIterations(n int) int {
	s := 0
	for i := 0; i < n; i++ {
		s += i & 1
	}
	return s
}

func bigSliceSum(n int) int {
	s := make([]int, n)
	for i := range s {
		s[i] = i
	}
	t := 0
	for _, v := range s {
		t += v
	}
	return t
}

func mapInsertions(n int) int {
	m := map[int]int{}
	for i := 0; i < n; i++ {
		m[i] = i
	}
	return len(m)
}

func stringBuild(n int) int {
	s := ""
	for i := 0; i < n; i++ {
		s += "x"
	}
	return len(s)
}

func main() {}
