package main

// Interface satisfaction compares method SIGNATURES, not just names
// (pre-merge audit 2026-07-31, finding 2: a name-only match reported
// satisfaction for types whose method has a different arity, parameter type,
// or result type).

type arityIface interface{ M(x int) int }

type arityT struct{ n int }

func (t arityT) M() int { return t.n }

func signatureArityMismatch() int {
	var a any = arityT{n: 3}
	_, ok := a.(arityIface)
	if ok {
		return 1
	}
	return 0
}

type paramIface interface{ P(x bool) int }

type paramT struct{ n int }

func (t paramT) P(x int) int { return t.n + x }

func signatureParamMismatch() int {
	var a any = paramT{n: 3}
	_, ok := a.(paramIface)
	if ok {
		return 1
	}
	return 0
}

type resultIface interface{ R() int8 }

type resultT struct{ n int }

func (t resultT) R() int { return t.n }

func signatureResultMismatch() int {
	var a any = resultT{n: 3}
	_, ok := a.(resultIface)
	if ok {
		return 1
	}
	return 0
}

type exactIface interface{ E(x int) int }

type exactT struct{ n int }

func (t exactT) E(x int) int { return t.n + x }

func signatureExactMatch() int {
	var a any = exactT{n: 3}
	v, ok := a.(exactIface)
	if !ok {
		return 0
	}
	return v.E(4)
}
