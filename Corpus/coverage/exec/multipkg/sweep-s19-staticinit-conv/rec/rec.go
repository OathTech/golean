package rec

// The recorder, one digit trace per chain; no initializer and no init of
// its own (a zero-valued map is no work), so rec is pruned and gates nothing.
var S map[string]int

// Push records an event on a chain and returns the mark.
func Push(chain string, m int) int {
	if S == nil {
		S = map[string]int{}
	}
	S[chain] = S[chain]*10 + m
	return m
}

