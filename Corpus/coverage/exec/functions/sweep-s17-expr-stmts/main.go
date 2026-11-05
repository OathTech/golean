package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-012's line): expression statements whose callee is not a plain
// identifier — an immediate func literal (void and result-discarding), an
// explicit generic instantiation, a parenthesised method value, a method
// call discarding two results, calls through a map element, a slice
// element, a struct field, a dereferenced func pointer and a call's result,
// an interface method call discarding two results, method expressions, a
// spread call, a stdlib call discarding its result, and bare calls inside a
// closure and a generic body; a source-through stdlib call discarding its
// result. Expected = gc go1.26.5.

import "strings"

var calls int

type counter struct{ n int }

func (c *counter) inc()           { c.n++ }
func (c *counter) two() (int, int) { c.n += 2; return c.n, c.n * 2 }
func (c counter) show() int       { calls += c.n; return c.n }

type twoer interface{ two() (int, int) }

type holder struct{ f func() int }

func idG[T any](x T) T { calls++; return x }

func dG[T any](x T) { idG(x) }

func sum(xs ...int) int {
	for _, x := range xs {
		calls += x
	}
	return calls
}

func two() (int, int) { calls++; return 1, 2 }

func upper(s string) string {
	calls++
	return s + s
}

// A3.4
func funclitStmtVoid() int {
	n := 0
	func() { n++ }()
	return n // 1
}

func funclitStmtDiscard() int {
	n := 0
	func() int { n += 2; return n }()
	return n // 2
}

// A3.5
func genericCallStmt() int {
	calls = 0
	idG[int](1)
	idG("a")
	return calls // 2
}

// A3.6
func methodValueCallStmt() int {
	c := &counter{}
	(c.inc)()
	return c.n // 1
}

func methodCallDiscard() int {
	c := &counter{}
	c.two()
	return c.n // 2
}

// A3.7
func callThroughMap() int {
	n := 0
	m := map[string]func() int{"a": func() int { n++; return n }}
	m["a"]()
	return n // 1
}

func callThroughSlice() int {
	n := 0
	fs := []func(){func() { n++ }}
	fs[0]()
	return n // 1
}

func callThroughField() int {
	n := 0
	s := holder{f: func() int { n++; return n }}
	s.f()
	return n // 1
}

func callThroughDeref() int {
	n := 0
	f := func() { n++ }
	pf := &f
	(*pf)()
	return n // 1
}

func callOfCall() int {
	n := 0
	mk := func() func() int { return func() int { n++; return n } }
	mk()()
	return n // 1
}

// A3.8
func ifaceCallDiscardTwo() int {
	c := &counter{}
	var i twoer = c
	i.two()
	return c.n // 2
}

// A3.9
func methodExprCallStmt() int {
	calls = 0
	c := counter{n: 5}
	counter.show(c)
	return calls // 5
}

func ptrMethodExprCallStmt() int {
	c := &counter{}
	(*counter).inc(c)
	return c.n // 1
}

// A3.10
func spreadCallStmt() int {
	calls = 0
	sum([]int{1, 2}...)
	return calls // 3
}

// A3.15 (a same-package function stands in for the stdlib member's shape;
// the stdlib twin is probed by hand under .tmp/probes/refusals)
func plainCallDiscardString() int {
	calls = 0
	upper("a")
	return calls // 1
}

// A3.15
func stdlibCallDiscard() int {
	strings.ToUpper("a")
	return len(strings.ToUpper("ab")) // 2
}

// A3.16
func discardInClosure() int {
	calls = 0
	f := func() { two() }
	f()
	return calls // 1
}

func discardInGeneric() int {
	calls = 0
	dG(1)
	dG("s")
	return calls // 2
}

func main() {
	println(funclitStmtVoid(), funclitStmtDiscard(), genericCallStmt(), methodValueCallStmt(), methodCallDiscard(),
		callThroughMap(), callThroughSlice(), callThroughField(), callThroughDeref(), callOfCall(), ifaceCallDiscardTwo(),
		methodExprCallStmt(), ptrMethodExprCallStmt(), spreadCallStmt(), plainCallDiscardString(), stdlibCallDiscard(), discardInClosure(),
		discardInGeneric())
}
