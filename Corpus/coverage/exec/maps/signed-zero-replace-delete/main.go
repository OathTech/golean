package main

// Signed-zero map key replacement, the -0-first direction plus a
// cross-sign delete: +0 == -0 is ONE key; inserting under +0 after -0
// overwrites the VALUE and (gc `needkeyupdate` for float kinds) the
// STORED KEY, so the surviving key is +0; delete under either sign
// removes the single entry. Complements floats/signed-zero-map-key
// (+0-first insert direction, no delete). Green cell from the external
// Codex review 2026-08-08
// (docs/2026-08-08_semantic-divergence-review.md §2).

func signedZeroReplaceDelete() int {
	posZero := 0.0
	negZero := -posZero
	m := map[float64]int{}
	m[negZero] = 1
	m[posZero] = 2 // replaces the value AND the stored key
	score := len(m) * 1000 // one entry
	score += m[negZero] * 100 // 2: either sign reads the entry
	for k := range m {
		if 1.0/k < 0 {
			score += 10 // NOT taken: stored key updated to +0
		}
	}
	delete(m, negZero) // cross-sign delete removes the +0-keyed entry
	return score + len(m) // 1200
}

func main() {
	signedZeroReplaceDelete()
}
