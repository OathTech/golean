package main

// make(map[K]V, hint): the hint is an ORDINARY OPERAND of the make call
// (spec#Making_slices_maps_and_channels lists it with the size arguments;
// spec#Order_of_evaluation orders its function calls and run-time panics
// with the surrounding operands), so its evaluation — side effects,
// panics, exactly-once — is observable; its VALUE is not: gc clamps a
// negative (or over-limit) hint to 0 and never panics on it
// (runtime/map.go makemap; latitude R16), and the spec calls the hint's
// effect implementation-dependent. BUG-082 (2026-09-02): the native
// frontend dropped the hint expression entirely, so none of the effects
// below happened in the machine. Every row here PASSES against gc after
// the fix (the born-red witness is builtins/make-maxalloc/map-hint-eval-
// order).

type hintSize int

// The hint's panic happens BEFORE the map is created: `created` stays 0.
func mapHintPanicMapNeverCreated() (result int) {
	created := 0
	defer func() {
		if recover() != nil {
			result = created*10 + 1
		}
	}()
	m := make(map[int]int, mapHintPanic())
	created = 1
	m[1] = 2
	return created*10 + len(m)
}

// The same panic, uncaught: the observed outcome is the panic itself.
func mapHintPanicUncaught() {
	m := make(map[int]int, mapHintPanic())
	m[1] = 2
}

func mapHintPanic() int {
	panic("map hint")
}

// A CALL-FREE panicking hint (an out-of-range index): no call to hoist,
// so the panic is raised by the machine's own evaluation of the hint
// operand, before the map exists.
func mapHintIndexPanicMapNeverCreated() (result int) {
	created := 0
	defer func() {
		if recover() != nil {
			result = created*10 + 1
		}
	}()
	s := []int{1, 2, 3}
	i := 5
	m := make(map[int]int, s[i])
	created = 1
	m[1] = 2
	return created*10 + len(m)
}

func mapHintIndexPanicUncaught() {
	s := []int{1, 2, 3}
	i := 5
	m := make(map[int]int, s[i])
	m[1] = 2
}

// The hint is evaluated exactly once.
func mapHintEvaluatedOnce() int {
	calls := 0
	m := make(map[int]int, mapHintCount(&calls, 4))
	m[1] = 2
	return calls*10 + len(m)
}

// A negative hint from a call: evaluated (the call counts), clamped (the
// map is an ordinary empty map that grows on insert).
func mapHintNegativeFromCall() int {
	calls := 0
	m := make(map[string]int, mapHintCount(&calls, -7))
	m["a"] = 1
	m["b"] = 2
	return calls*100 + len(m)*10 + m["b"]
}

func mapHintCount(p *int, v int) int {
	*p = *p + 1
	return v
}

// A zero hint.
func mapHintZero() int {
	m := make(map[int]int, 0)
	m[1] = 1
	m[2] = 2
	return len(m)
}

// A hint of a NAMED integer type (spec: "of integer type").
func mapHintNamedIntType() int {
	var s hintSize = 3
	m := make(map[int]bool, s)
	m[1] = true
	m[2] = false
	return len(m)
}

// A hint of an unsigned type (uint8: still "of integer type").
func mapHintUint8Var() int {
	var u uint8 = 200
	m := make(map[uint8]int, u)
	m[u] = 1
	return len(m) + int(u)
}

// An untyped constant hint (a named constant expression, not a literal —
// builtins/make-map-hint covers the literal 8).
func mapHintUntypedConst() int {
	const n = 1 << 4
	m := make(map[int]int, n)
	m[n] = n
	return len(m)*100 + m[n]
}

// A TYPED constant of a named integer type.
func mapHintTypedConst() int {
	const s hintSize = 5
	m := make(map[int]int, s)
	m[int(s)] = 7
	return len(m)*10 + m[5]
}

// Order: a preceding statement's call, the hint's call, then the index
// and value calls of the first insert — logged as decimal digits.
func mapHintEvalOrderWithNeighbors() int {
	log := 0
	a := mapHintLog(&log, 1)
	m := make(map[int]int, mapHintLog(&log, 2))
	m[mapHintLog(&log, 3)] = mapHintLog(&log, 4)
	return log*10 + len(m) + a
}

// Order inside ONE expression: the hint's call is a function call of the
// left operand, so it precedes the right operand's call
// (spec#Order_of_evaluation: calls in lexical left-to-right order).
func mapHintInExpression() int {
	log := 0
	x := len(make(map[int]int, mapHintLog(&log, 5))) + mapHintLog(&log, 6)
	return log*10 + x
}

func mapHintLog(p *int, d int) int {
	*p = *p*10 + d
	return d
}

func main() {
	mapHintEvaluatedOnce()
}
