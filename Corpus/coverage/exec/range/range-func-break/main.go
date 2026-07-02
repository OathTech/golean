package main

func rangeFuncBreak() int {
	// Go 1.23+: breaking from the loop makes yield return false.
	calls := 0
	seq := func(yield func(int) bool) {
		for i := 1; i <= 5; i++ {
			calls++
			if !yield(i) {
				return
			}
		}
	}
	sum := 0
	for v := range seq {
		sum += v
		if v == 2 {
			break
		}
	}
	return calls*100 + sum
}
