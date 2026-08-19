package main

// BUG-005 membership row (2026-08-19 ruling — memo §5: cases
// exercising created-entry latitude ride membership rows). The RAW
// latitude observable the strict sibling maps/added-entries-bound
// deliberately normalizes away: one start key, the body creates one
// entry during iteration, and the subject returns the production
// count n itself.
//
// spec#For_statements (range clause, maps): "If a map entry is
// created during iteration, that entry may be produced during the
// iteration or may be skipped. The choice may vary for each entry
// created and from one iteration to the next." So the admitted set is
// exactly {1, 2}: key 1 is a never-removed start key (mandatory,
// produced exactly once — the spec-forced traversal clause), and the
// created entry 2 may be produced (n=2) or skipped (n=1); created
// once, never deleted, it is producible at most once.
//
// PRE-SURGERY COLOR: RED, deliberately (pinned on BUG-005's Cases
// line). The snapshot machine resolves the created-entries latitude
// to the singleton "never produced" — its enumerated set is {1}, and
// the membership lint refuses a singleton-set membership row. The (L)
// surgery makes the machine realize both members; this row flips
// green there and thereafter fails loudly if the machine ever
// over-produces (n>2), invents keys, or diverges.

func mapAddedEntryCount() int {
	m := map[int]int{1: 10}
	n := 0
	for k := range m {
		n++
		if n > 5 {
			return -2 // outside every member of the ruled envelope
		}
		switch k {
		case 1:
			m[2] = 20 // created during iteration: may be produced or skipped
		case 2:
			// produced created entry: counted via n
		default:
			return -3 // a key the map never held: outside the envelope
		}
	}
	return n
}

func main() {
	println(mapAddedEntryCount())
}
