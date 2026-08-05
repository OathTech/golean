package main

// Signed zeros as map keys (floats design note 2026-08-04 §4): +0 == -0
// under Go's ==, so they are ONE key — and on update gc OVERWRITES the
// stored key (`needkeyupdate` is true for float kinds), so inserting
// under -0 after +0 leaves -0 as the stored key. The stored key's sign
// is observed through range + 1/k, both int-valued.
func floatSignedZeroMapKey() int {
	posZero := 0.0
	negZero := -posZero
	m := map[float64]int{}
	m[posZero] = 1
	m[negZero] = 2
	score := len(m) * 100  // one key
	score += m[posZero] * 10 // value overwritten by the -0 insert
	for k := range m {
		if 1.0/k < 0 {
			score += 1 // stored key is -0
		}
	}
	return score
}

func main() {
	floatSignedZeroMapKey()
}
