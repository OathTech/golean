package main

// raft-proofs' ask G21 (2), the local space (2026-10-26; the [USER]'s relay
// of the same day; lane core/g21-normal-form-spill-1026): a []byte(s) or
// []rune(s) conversion whose fresh backing would be past the interpreter's
// footprint budget (arrayFootprintBudget, 1<<24 scalar leaves — one leaf per
// byte or rune) is REFUSED BY NAME at the conversion (cause
// unsupported:conv-footprint-budget, scripts/machine-causes.tsv), after the
// capacity consult — the REALIZED capacity is charged, the make site's guard
// at the door BUG-131's scope sentence (2) named — before any backing is
// built. Before the guard the conversion BUILT its backing cell by cell and
// died under the box's memory cap (exit 137 under CAPPED_MEM_MAX=256M for
// bytesOverBudget on the base's binary; BUG-131's review F1 measured a
// 2^26-byte string killed at 4G). gc allocates and answers. The strings are
// built by doubling (a string is one compact value in the model; only its
// conversion materializes one cell per element).
//
//   bytesOverBudget — a string of 2^24 + 1 bytes (one past the budget),
//                     []byte(s): 2^24 + 1 cells, over the budget. RED BY
//                     DESIGN (gc 16777217).
//   runesOverBudget — the same string, []rune(s): 2^24 + 1 cells. RED BY
//                     DESIGN (gc 16777217).
//   bytesInBudget   — a 2^20-byte string, []byte(s): inside the budget, PASS.
//   runesInBudget   — a 2^20-byte string, []rune(s): inside the budget, PASS.

func doubled(k int) string {
	s := "a"
	for i := 0; i < k; i++ {
		s += s
	}
	return s
}

func bytesOverBudget() int {
	b := []byte(doubled(24) + "x")
	return len(b) + int(b[0]-'a')
}

func runesOverBudget() int {
	r := []rune(doubled(24) + "x")
	return len(r) + int(r[0]-'a')
}

func bytesInBudget() int {
	b := []byte(doubled(20))
	return len(b) + int(b[0]-'a') + int(b[len(b)-1]-'a')
}

func runesInBudget() int {
	r := []rune(doubled(20))
	return len(r) + int(r[0]-'a') + int(r[len(r)-1]-'a')
}

func main() {
	println(bytesInBudget(), runesInBudget())
}
