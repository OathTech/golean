package main

// S23 sweep — resource budgets (docs/defect-shapes.md; the plan
// docs/2026-10-27_defect-neighbourhood-campaign.md §4; lane sweep/s23-budgets,
// 2026-11-05): the `append` door beside the doubling rows of
// arrays/materialization-budget-append/. The spill guard
// (appendSpillFootprintCheck, GoLean/GoCore/Machine.lean) charges the REALIZED
// capacity after gc's growslice panic and the capacity consult, so the
// refusal fires at the growth step whose realized backing crosses 2^24 scalar
// leaves, whatever the element count asked for; the string spread lowers to
// the conversion door ([]byte(s), convFootprintCheck); a spread of a make meets
// the make site's guard first. gc allocates and answers on every row.
//
//   appendOneAtATimeOver     — [1<<16]byte elements appended one at a time: the
//                              doubling ladder up to 256 is admitted (256 × 2^16
//                              = the budget), the growth to 512 at the 257th
//                              append is refused by name (gc 2571). RED BY DESIGN
//                              (unsupported:append-footprint-budget, BUG-131).
//   appendNearBudgetOneMore  — 16000 rows of [1024]byte (16.4M leaves, admitted)
//                              plus ONE element: the realized growth (gc's
//                              1.25× ladder, 20192 rows) is over the budget
//                              (gc 160023). RED BY DESIGN (BUG-131).
//   appendSpreadMakeOver     — append(s, make([][1024]byte, n)...) with the make
//                              over the budget: the make site refuses first
//                              (unsupported:make-footprint-budget-runtime;
//                              BUG-131). gc 32770.
//   copyControl              — copy builds no backing: 4096 bytes into a 2^16
//                              backing, PASS.
//   appendStringSpreadOver   — append([]byte(nil), s...) with s one byte past the
//                              budget: the spread is the conversion door
//                              (unsupported:conv-footprint-budget; BUG-131).
//                              gc 16777217.
//   appendStringSpreadInBudget — the same spread at 2^20 bytes onto a two-byte
//                              slice, PASS.

func appendOneAtATimeOver() int {
	var s [][1 << 16]byte
	for i := 0; i < 257; i++ {
		var e [1 << 16]byte
		e[0] = byte(i)
		s = append(s, e)
	}
	return len(s)*10 + int(s[256][0]-s[255][0])
}

func appendNearBudgetOneMore() int {
	s := make([][1024]byte, 16000)
	s[15999][1023] = 3
	var e [1024]byte
	e[0] = 9
	s = append(s, e)
	return len(s)*10 + int(s[16000][0]) + int(s[15999][1023])
}

func appendSpreadMakeOver() int {
	n := 1 << 15
	s := make([][1024]byte, 2)
	s = append(s, make([][1024]byte, n)...)
	return len(s)
}

func copyControl() int {
	dst := make([]byte, 1<<16)
	src := make([]byte, 4096)
	src[4095] = 9
	n := copy(dst, src)
	return n + int(dst[4095]) + len(dst)
}

func doubled(k int) string {
	s := "a"
	for i := 0; i < k; i++ {
		s += s
	}
	return s
}

func appendStringSpreadOver() int {
	s := doubled(24) + "x"
	b := append([]byte(nil), s...)
	return len(b) + int(b[len(b)-1]-'a')
}

func appendStringSpreadInBudget() int {
	s := doubled(20)
	b := append([]byte("xy"), s...)
	return len(b) + int(b[0]-'a') + int(b[len(b)-1]-'a')
}

func main() {
	println(copyControl(), appendStringSpreadInBudget())
}
