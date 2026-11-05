package main

// S23 sweep — resource budgets (docs/defect-shapes.md; the plan
// docs/2026-10-27_defect-neighbourhood-campaign.md §4; lane sweep/s23-budgets,
// 2026-11-05): array TYPES at the declaration sites the quarantine rows of
// 2026-10-13 (arrays/materialization-budget-quarantine*/: a literal, a global,
// a defined type with a method, a constant make) leave out. The frontend
// applies the budgets per declaration (tools/nativefrontend/budgets.go): a
// function whose body names an over-budget type becomes its stub and refuses
// by name when run (FAIL/frontend-export, by-design/materialization-budget);
// a declared type that REACHES a violation ships as a marker and every user
// refuses. gc builds and answers on every row. The over-budget rows are RED
// BY DESIGN on BUG-078's Cases line; unit-nesting-65 is BUG-412's.
//
//   localOver / localSibling — a local variable of [70000]int (past
//                              arrayLenBudget, 2^16); the sibling with [65536]int
//                              runs: the quarantine is per function.
//   fieldOver                — a struct field of [70000]int: the struct reaches
//                              the violation; a user that never touches the field
//                              refuses all the same.
//   fieldsSumOver / At       — two fields of [4096][2048]byte and [4096][2049]byte
//                              SUM past the footprint budget (2^24 + 4096 leaves);
//                              the twin at exactly 2^24 is admitted (2 s).
//   definedChainOver         — type Row [4096]byte; type Grid [4097]Row: the
//                              footprint through a defined element.
//   paramOver / returnOver   — the over-budget type as a parameter (through a
//                              defined name) and as a return type.
//   mapValueOver             — map[int][70000]int: the type reaches the violation.
//   newOver / newAtDim       — new([70000]int) refuses; new([65536]byte) runs.
//   deepNestingOver          — [2]^25 byte: 2^25 leaves through 25 levels.
//   unitNesting64 / 65       — [1]^64 int and [1]^65 int: a footprint of ONE leaf
//                              at 64 and 65 levels. The frontend's footprint walk
//                              saturates past depth 64 and refuses the 65-level
//                              type as if it were over budget (BUG-412: a legal
//                              program refused with a text naming a footprint of
//                              2^63 − 1); gc builds both and answers 8.
//   pointerLeaves            — [65536]*int: one leaf per pointer, admitted.
//   indexKeyedLiteralOver    — [...]byte{70000: 1}: the literal's type has 70001
//                              elements.

type Holder struct {
	a [70000]int
	n int
}

type Two struct {
	a [4096][2048]byte
	b [4096][2049]byte
}

type TwoAt struct {
	a [4096][2048]byte
	b [4096][2048]byte
}

type Row [4096]byte
type Grid [4097]Row

type Big [70000]int

type Unit64 [1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1]int
type Unit65 [1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1]int

func takes(b Big) int { return b[0] }

func gives() [70000]int {
	var a [70000]int
	a[1] = 1
	return a
}

func localOver() int {
	var a [70000]int
	a[1] = 2
	return len(a) + a[1]
}

func localSibling() int {
	var a [65536]int
	a[1] = 2
	return len(a) + a[1]
}

func fieldOver() int {
	var h Holder
	h.n = 3
	return h.n
}

func fieldsSumOver() int {
	var t Two
	t.a[0][0] = 1
	t.b[4095][2048] = 2
	return len(t.a) + int(t.a[0][0]) + int(t.b[4095][2048])
}

func fieldsSumAt() int {
	var t TwoAt
	t.a[0][0] = 1
	t.b[4095][2047] = 2
	return len(t.a) + int(t.a[0][0]) + int(t.b[4095][2047])
}

func definedChainOver() int {
	var g Grid
	g[4096][4095] = 1
	return len(g) + int(g[4096][4095])
}

func paramOver() int {
	var b Big
	b[0] = 4
	return takes(b)
}

func returnOver() int {
	a := gives()
	return len(a) + a[1]
}

func mapValueOver() int {
	m := map[int][70000]int{}
	m[1] = [70000]int{}
	return len(m) + len(m[1])
}

func newOver() int {
	p := new([70000]int)
	p[2] = 3
	return len(p) + p[2]
}

func newAtDim() int {
	p := new([65536]byte)
	p[65535] = 3
	return len(p) + int(p[65535])
}

func deepNestingOver() int {
	var a [2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2][2]byte
	a[1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1] = 5
	return len(a) + int(a[1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1][1])
}

func unitNesting64() int {
	var d Unit64
	d[0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0] = 7
	return len(d) + d[0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0]
}

func unitNesting65() int {
	var d Unit65
	d[0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0] = 7
	return len(d) + d[0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0][0]
}

func pointerLeaves() int {
	var a [65536]*int
	a[0] = new(int)
	*a[0] = 5
	return len(a) + *a[0]
}

func indexKeyedLiteralOver() int {
	a := [...]byte{70000: 1}
	return len(a) + int(a[70000])
}

func main() {
	println(localSibling(), fieldsSumAt(), newAtDim(), unitNesting64(), pointerLeaves())
}
