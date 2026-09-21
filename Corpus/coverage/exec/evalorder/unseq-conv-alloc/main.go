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
//
// The Stage E audit fix round (2026-09-21; docs/2026-09-21_unseq-stage-e-audit.md): F1 — Go 1.26
// `new(x)` (spec#Allocation) inside an admitted sweep was lowered as `new(T)` with the zero
// value, dropping the initializer and any call inside it (a WRONG ANSWER against gc and main; no
// corpus row reached it). The argument is now an operand of the E1-ordered `new` call: its reads
// occurrences inside new's window, its calls E1-ordered events, the allocation storing its value.
// new-expr-vs-call and new-call-vs-call are the audit's two witnesses, born FAIL on the candidate
// (5; `g` 103) → PASS here. F4 — `string([]byte)` / `string([]rune)` READ the slice's backing
// array at the conversion: an occurrence of its own (the first cut sent `string(b) + m()` to the
// legacy path as «every edge forced» — a pin of gc's order); string-bytes-vs-call and
// string-runes-vs-call envelope it, gc's zb inside.

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

// AUDIT FIX ROUND F1, witness 1 (the audit's f1-new-expr-litmus): `*new(x) + m()` with m writing the
// captured x (1 → 10, returns 5). Go 1.26 `new(x)` allocates a variable initialized to x's VALUE; new
// is an E1-ordered call, so x's read inside its window is forced before m: 1 + 5 = 6 on every stream
// (the fresh pointer's dereference is the sweep's observable occurrence — its order against m
// changes nothing). gc 6; main 6; the E4 candidate 5 (the zero value). STRICT.
func newExprVsCall() int {
	x := 1
	m := mut(&x, 10)
	return *new(x) + m()
}

func mPrint() int { println("m"); return 7 }
func gPrint() int { println("g"); return 1 }

// AUDIT FIX ROUND F1, witness 2 (the audit's f1-new-call-dropped-litmus): `*new(mPrint()) + x + h() +
// gPrint()` with h writing the captured x (1 → 2, returns 100). mPrint, new, h and gPrint are E1-ordered
// (mPrint inside new's window); x's read is spec-unsequenced against the calls — before h 7 + 1 + 100 +
// 1 = 109, after h 110; the output is `m` then `g` on both. gc `m` `g` 110; main the same; the E4
// candidate `g` 103 (mPrint never ran). {109, 110}.
func newCallVsCall() int {
	x := 1
	h := func() int { x = 2; return 100 }
	return *new(mPrint()) + x + h() + gPrint()
}

// AUDIT FIX ROUND F4 (the audit's probe d1): `string(b) + m()` with b private but ALIASED by c, m
// writing c[0] ('a' → 'z'): the conversion copies b's backing array at the conversion — a mutable
// read spec-unsequenced against m — before m "ab", after "zb". gc "zb" (OBYTES2STR is not in
// order.go's call class: the conversion runs after the call). {ab, zb}.
func stringBytesVsCall() string {
	b := []byte("ab")
	c := b
	m := func() string { c[0] = 'z'; return "" }
	return string(b) + m()
}

// AUDIT FIX ROUND F4 (the audit's probe a6): the same on `[]rune`. {ab, zb}; gc "zb".
func stringRunesVsCall() string {
	r := []rune("ab")
	c := r
	m := func() string { c[0] = 'z'; return "" }
	return string(r) + m()
}

func main() {
	println(convReadVsCall())
	println(structLitVsCall())
	println(addrLitVsCall())
	println(sliceLitVsCall())
	println(makeLenVsCall())
	println(mapLitControl())
	println(newExprVsCall())
	println(newCallVsCall())
	println(stringBytesVsCall())
	println(stringRunesVsCall())
}
