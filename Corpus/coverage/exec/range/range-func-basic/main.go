package main

func rangeFuncBasic() int {
	// Go 1.23+: range accepts iterator functions.
	seq := func(yield func(int) bool) {
		for i := 1; i <= 3; i++ {
			if !yield(i * 10) {
				return
			}
		}
	}
	out := 0
	for v := range seq {
		out = out*100 + v
	}
	return out
}
