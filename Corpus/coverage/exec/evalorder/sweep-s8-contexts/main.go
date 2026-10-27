package main

// Sweep S8 (lane sweep/s8-unseq, 2026-10-27): contexts × kinds — the same unsequenced
// pair (a read beside a call that mutates what it reads) inside a method body, a stored /
// immediately-invoked / deferred func literal's body, a generic body, a named-result
// function, a loop body. Membership rows where the grammar admits the sweep (method
// bodies, named results, loop bodies); strict rows where the lifted or generic body is
// declined and the legacy call-first order is gc's. The EARLY kinds in the declined
// bodies are BUG-310's rows (sweep-s8-early-kinds-legacy); the generic `[]byte` rows
// BUG-313's (sweep-s8-generic-conv).

type M struct {
	x  int
	iv any
	s  string
}

func (m *M) setX() int  { m.x = 5; return 10 }
func (m *M) setIv() int { m.iv = 5; return 10 }
func (m *M) setS() int  { m.s = "zz"; return 1 }

func (m *M) bodyField() int     { return m.x + m.setX() }
func (m *M) bodyAssertion() int { return m.iv.(int) + m.setIv() }
func (m *M) bodyBytesConv() int { return int([]byte(m.s)[0]) + m.setS() }

func methodBodyField() int     { m := &M{x: 1}; return m.bodyField() }
func methodBodyAssertion() int { m := &M{iv: 1}; return m.bodyAssertion() }
func methodBodyBytesConv() int { m := &M{s: "ab"}; return m.bodyBytesConv() }

// --- a stored func literal's body ---

func closureLocalVar() int {
	x := 1
	set := func() int { x = 5; return 10 }
	fn := func() int { return x + set() }
	return fn()
}

func closureIndex() int {
	s := []int{1, 5}
	i := 0
	set := func() int { i = 1; return 10 }
	fn := func() int { return s[i] + set() }
	return fn()
}

func closureDeref() int {
	x, y := 1, 5
	p := &x
	red := func() int { p = &y; return 10 }
	fn := func() int { return *p + red() }
	return fn()
}

func closureBytesConv() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	fn := func() int { return int([]byte(s)[0]) + set() }
	return fn()
}

// --- an immediately-invoked literal's body ---

func invokedLitBytesConv() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	return func() int { return int([]byte(s)[0]) + set() }()
}

func invokedLitLocalVar() int {
	x := 1
	set := func() int { x = 5; return 10 }
	return func() int { return x + set() }()
}

// --- a deferred literal's body ---

func deferredLitBytesConv() int {
	r := 0
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	func() {
		defer func() { r = int([]byte(s)[0]) + set() }()
	}()
	return r
}

func deferredLitLocalVar() int {
	r := 0
	x := 1
	set := func() int { x = 5; return 10 }
	func() {
		defer func() { r = x + set() }()
	}()
	return r
}

// --- generic bodies (a T result declines the sweep: legacy, call-first = gc) ---

func genParamRead[T int | int64](x T, set func() T) T { return x + set() }

func genericParamRead() int {
	x := 1
	set := func() int { x = 5; return 10 }
	return int(genParamRead(x, set))
}

func genDeref[T int | int64](p *T, set func() T) T { return *p + set() }

func genericDeref() int {
	x := 1
	set := func() int { x = 5; return 10 }
	return int(genDeref(&x, set))
}

func genIndex[T int | int64](s []T, pi *int, set func() T) T { return s[*pi] + set() }

func genericIndex() int {
	s := []int{1, 5}
	i := 0
	set := func() int { i = 1; return 10 }
	return genIndex(s, &i, set)
}

func genAssertToT[T int | int64](piv *any, set func() T) T { return (*piv).(T) + set() }

func genericAssertToTypeParam() int {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	return genAssertToT(&iv, set)
}

// --- a named result, a loop body ---

func namedResultAssertion() (r int) {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	r = iv.(int) + set()
	return
}

func loopBodyAssertion() int {
	var iv any
	set := func() int { iv = 5; return 10 }
	t := 0
	for _, v := range []int{1, 1} {
		iv = v
		t += iv.(int) + set()
	}
	return t
}
