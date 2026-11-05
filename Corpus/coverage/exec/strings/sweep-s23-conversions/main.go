package main

// S23 sweep — resource budgets (docs/defect-shapes.md; the plan
// docs/2026-10-27_defect-neighbourhood-campaign.md §4; lane sweep/s23-budgets,
// 2026-11-05): the conversion doors beside arrays/materialization-budget-conv/
// (one byte past the budget / 2^20 in budget): the budget's edge from the
// admitted side, the code-point count of a multi-byte string, the reverse
// conversions string(rs) / string(b) (a whole-backing read, Mem.loadElems),
// and the slice→array conversions, whose array TYPE is what the budgets see.
// gc answers on every row.
//
//   bytesAtBudget    — []byte(s) at exactly 2^24 bytes: admitted (strict `>`
//                      on the realized capacity), PASS.
//   runesMultibyte   — []rune of 2^20 three-byte runes: the count is code
//                      points (2^20 leaves), PASS.
//   stringOfRunes    — string(rs) over 2^18 two-byte runes, PASS.
//   stringOfBytes    — string(b) over a 2^20-byte backing, PASS.
//   toArrayOver      — [70000]byte(b): the array type is past arrayLenBudget
//                      (2^16), the subject quarantines by name BEFORE the
//                      machine's own frontier refusal of slice-to-array
//                      conversions (`[65536]byte(b)` and `(*[65536]byte)(b)` at
//                      an admitted type refuse by name as the triage L2b
//                      frontier — probed, recorded as gaps, not rowed). RED BY
//                      DESIGN (FAIL/frontend-export,
//                      by-design/materialization-budget; BUG-078 Cases). gc 70005.

func doubled(k int) string {
	s := "a"
	for i := 0; i < k; i++ {
		s += s
	}
	return s
}

func bytesAtBudget() int {
	b := []byte(doubled(24))
	return len(b) + int(b[0]-'a') + int(b[len(b)-1]-'a')
}

func runesMultibyte() int {
	s := "€"
	for i := 0; i < 20; i++ {
		s += s
	}
	rs := []rune(s)
	return len(rs)*10 + len(s)/len(rs) + int(rs[len(rs)-1]-'€')
}

func stringOfRunes() int {
	s := "é"
	for i := 0; i < 18; i++ {
		s += s
	}
	rs := []rune(s)
	t := string(rs)
	return len(rs)*100 + len(t) - len(s) + int(rs[len(rs)-1]-'é')
}

func stringOfBytes() int {
	n := 1 << 20
	b := make([]byte, n)
	b[n-1] = 7
	s := string(b)
	return len(s) + int(s[n-1])
}

func toArrayOver() int {
	b := make([]byte, 70000)
	b[69999] = 5
	a := [70000]byte(b)
	return len(a) + int(a[69999])
}

func main() {
	println(runesMultibyte(), stringOfRunes(), stringOfBytes())
}
