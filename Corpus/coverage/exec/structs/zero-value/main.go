package main

type zeroValueStruct struct {
	n int
	s string
	b bool
}

func structZeroValue() int {
	var z zeroValueStruct
	score := z.n + len(z.s)*10
	if !z.b {
		score += 100
	}
	return score
}

func main() {
	structZeroValue()
}
