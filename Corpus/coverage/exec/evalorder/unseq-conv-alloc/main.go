package main

// Stage E of the evaluation-order model v2.1, family E4 (lane core/unseq-stage-e-0921,
// 2026-09-21): CONVERSIONS and ALLOCATIONS. A conversion `T(x)` is a PURE OP over its
// operand's value (never an occurrence of its own — the machine's `convert` and the
// string/byte/rune operators cannot fail inside the admitted type grammar); a COMPOSITE
// LITERAL (`T{…}`, `&T{…}`, `[]T{…}`) carries NO E1 edge (v2.1 R3 — spec#Order_of_evaluation
// orders calls, method calls, receives and logical operations; a literal is none of those):
// its payload reads are the occurrences, spec-unsequenced against the sibling calls;
// `make`/`new` are FUNCTION CALLS (spec#Built-in_functions «called like any other function»)
// — E1 participants like len/cap ([AGENT] choice, design §E4; the strict control below is
// its test against gc). References: enumerate.py E4a–E4e; the wires Tests/unseq-wire/
// e4alloc.json + native-{e4alloc,e4conv}.json. gc's draws are call-first (the literal's
// payload read after the call; the conversion operand's read BEFORE the call — E12's
// recorded exception, retired here into the set).

type T struct{ x int }

func mut(p *int, v int) func() int {
	return func() int { *p = v; return 5 }
}

// E4a: int([]byte(s)[0]) + m(), s captured (m: s = "zz", returns 1): the read of s before m
// → 'a' + 1 = 98, after → 'z' + 1 = 123. {98, 123}.
func convReadVsCall() int {
	s := "ab"
	m := func() int { s = "zz"; return 1 }
	return int([]byte(s)[0]) + m()
}

// A VALUE struct literal's payload read beside the call that writes it: T{x: x}.x + m()
// (m: x = 10, returns 5) → before 1 + 5 = 6, after 10 + 5 = 15. {6, 15}.
func structLitVsCall() int {
	x := 1
	m := mut(&x, 10)
	return T{x: x}.x + m()
}

// `&T{x: x}` — the literal an `allocate` body (`new`) on the payload's cell; the field read through
// the fresh pointer. {6, 15}.
func addrLitVsCall() int {
	x := 1
	m := mut(&x, 10)
	return (&T{x: x}).x + m()
}

// A slice literal's payload read beside the call: []int{x}[0] + m(). {6, 15}.
func sliceLitVsCall() int {
	x := 1
	m := mut(&x, 10)
	return []int{x}[0] + m()
}

// STRICT CONTROL for «make is a function call»: len(make([]int, n)) + m() with m writing the
// captured n (1 → 3, returns 5): make is E1-ordered BEFORE m and n's read lies inside make's
// operand — forced before m: 1 + 5 = 6 on every stream. gc's draw decides the modeling.
func makeLenVsCall() int {
	n := 1
	m := mut(&n, 3)
	return len(make([]int, n)) + m()
}

// STRICT CONTROL: a MAP literal stays on the legacy path by name (E5 — gc evaluates its
// dynamic entries at the literal's position); both orders agree here (m writes nothing the
// literal reads). 1 + 5 = 6.
func mapLitControl() int {
	x := 1
	m := mut(&x, 10)
	return map[int]int{7: 1}[7] + m()
}

func main() {
	println(convReadVsCall())
	println(structLitVsCall())
	println(addrLitVsCall())
	println(sliceLitVsCall())
	println(makeLenVsCall())
	println(mapLitControl())
}
