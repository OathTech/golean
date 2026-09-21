package main

// Unit tests for the Stage C whole-sweep decision procedure (unseq.go,
// `unseqClassify`): the pilot grammar's admitted shapes — every reference
// witness the native pilot lowers (W1/W2/W3/W5/W6, R1/R2a-c/R4/R6, the
// BUG-101, BUG-104 and BUG-102 flip rows) — and the refusals BY REASON at
// the boundary (map targets, receives, methods, derefs, conversions,
// multi-target forms, call-free and read-free sweeps); Stage E E1 (2026-09-21)
// adds the package-level variables — reads, compound targets, the BUG-113
// shapes — as admitted witnesses and a global of a type outside the grammar
// as a refusal by name. The
// classifier is the ONE implementation the census and the emitter share,
// so a shape admitted here is a shape the emitter lowers as an `unseq`
// graph, and a reason named here is the reason the census prints.

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

// classifySource type-checks a single-file main package and classifies
// EVERY statement of the named function's body (its top-level statement
// list only), in order.
func classifySource(t *testing.T, src, fn string) []unseqDecision {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "main.go", src, 0)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info := newTypesInfo()
	conf := types.Config{Importer: importer.Default()}
	pkg, err := conf.Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatalf("type-check: %v", err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	for _, d := range f.Decls {
		fd, ok := d.(*ast.FuncDecl)
		if !ok || fd.Name.Name != fn || fd.Body == nil {
			continue
		}
		sig := info.Defs[fd.Name].Type().(*types.Signature)
		ctx := &unseqCtx{body: fd.Body, captured: nil, results: sig.Results()}
		out := []unseqDecision{}
		for _, s := range fd.Body.List {
			out = append(out, e.unseqClassify(s, ctx))
		}
		return out
	}
	t.Fatalf("function %s not found", fn)
	return nil
}

// decisionAt returns the classification of the function's statement
// `fromEnd` positions before the end (0 = the last statement).
func decisionAt(t *testing.T, src, fn string, fromEnd int) unseqDecision {
	t.Helper()
	ds := classifySource(t, src, fn)
	return ds[len(ds)-1-fromEnd]
}

const unseqWitnessSrc = `package main

var g int
var gf float64
var left = false

func sinkL(b bool, n int) { println("logical", b, n) }
func sinkR(n int, b bool) { println("logical", n, b) }
func setG() int { g = 10; return 1 }

type T struct{ x int }

func (t *T) M() int { return 7 }

func wit(x int) int { println("wit", x); return x }
func fnine() int { println("f"); return 9 }
func sink(a, b int) int { return a + b }
func sinkB(b bool, n int) {}
func two() (int, int) { return 1, 2 }
func b2i(b bool) int { if b { return 1 }; return 0 }
func va(xs ...int) int { return len(xs) }
func gen[T any](x T) T { return x }

// W1: v := mut() + a, a CAPTURED by mut.
func w1() int {
	a := 1
	mut := func() int { a = 2; return 0 }
	v := mut() + a
	return v
}

// W6: x + inc() + inc(), x captured.
func w6() int {
	x := 0
	inc := func() int { x++; return 0 }
	return x + inc() + inc()
}

// R1: x + y + mut(), both captured.
func r1() int {
	x, y := 0, 0
	mut := func() int { x = 1; y = 2; return 0 }
	return x + y + mut()
}

// R6: a[f()] with a a captured slice (header read + index producer + one checked access).
func r6() int {
	a := []int{10}
	f := func() int { a = []int{20}; return 0 }
	return a[f()]
}

// W2: a[b[0]] + mut(), captured slices.
func w2() int {
	a := []int{10, 20}
	b := []int{0}
	mut := func() int { a[0] = 30; a[1] = 40; b[0] = 1; return 0 }
	return a[b[0]] + mut()
}

// W3: a[i] += mut(), i captured; a private (its ELEMENTS are heap).
func w3() {
	a := []int{10, 20}
	i := 0
	mut := func() int { i = 1; return 1 }
	a[i] += mut()
}

// W5: println(a[0] + mut()) in a loop, a captured.
func w5() {
	a := []int{7}
	mut := func() int { a = nil; return 0 }
	for n := 0; n < 2; n++ {
		println(a[0] + mut())
	}
}

// R4: old := a; a[0] += mut() with mut rebinding a.
func r4() {
	a := []int{10, 20}
	b := []int{100, 200}
	old := a
	mut := func() int { a = b; return 1 }
	a[0] += mut()
	println(old[0], a[0])
}

// R2a: sink(z || h(), k()) — a guard whose region holds an event, a later sibling event.
func r2a() {
	z := true
	h := func() bool { println("h"); return true }
	k := func() int { println("k"); return 7 }
	sinkB(z || h(), k())
}

// R2b: sink(left || b, change()) — E1 anchored at the completion.
func r2b() {
	left, b := false, false
	change := func() int { b = true; return 0 }
	sinkB(left || b, change())
}

// R2c: sink(g(), a || (b && h()), k()) — nested guards, an earlier call.
func r2c() {
	a, b := false, true
	gg := func() int { a = true; return 1 }
	h := func() bool { return true }
	k := func() int { return 7 }
	sink(gg(), b2i(a||(b&&h()))+k())
}

// BUG-101 row 1: iv.(int) + len(b[j:]) + f(), iv captured, the assertion succeeds early.
func bug101a() int {
	var iv interface{} = 3
	b := make([]int, 2)
	j := 0
	return iv.(int) + len(b[j:]) + func() int { iv = "s"; println("mut"); return 1 }()
}

// BUG-101 row 2: a[i:][0] + len(b[j:]) + f(), i captured.
func bug101b() int {
	a := []int{10, 20}
	b := []int{1, 2}
	i := 0
	j := 0
	return a[i:][0] + len(b[j:]) + func() int { i = 1; println("mut"); return 0 }()
}

// BUG-104 row 1: x[fnine()] += wit(5) — a call-bearing compound target.
func bug104a() int {
	x := make([]int, 1)
	x[fnine()] += wit(5)
	return x[0]
}

// BUG-102: x[fnine()] += len(b[j]) + wit(5) — len as an E1 event beside the calls.
func bug102() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	x[fnine()] += len(b[j]) + wit(5)
	return x[0]
}

// A call statement whose argument holds a checked access: forced (arg before call), admitted.
func forcedArg() int {
	t := []int{1, 2}
	k := 5
	return wit(t[k])
}

// return two() — a two-result invocation in the return position.
func retTwo() (int, int) {
	s := []int{1}
	_ = s
	return two()
}

// --- the boundary: legacy by reason ---

func mapTarget() int {
	m := map[int]int{}
	t := []int{1}
	k := 5
	m[t[k]] += wit(5)
	return len(m)
}

func recvOperand() int {
	x := make([]int, 1)
	ch := make(chan int, 1)
	ch <- 3
	x[fnine()] += <-ch
	return x[0]
}

func methodCall() int {
	q := &T{}
	s := []int{1}
	return s[0] + q.M()
}

func derefRead() int {
	x := 1
	p := &x
	return *p + wit(1)
}

// --- Stage E E1: package-level variables are READ occurrences / operand-free targets ---

// A global read beside a call: admitted (the read is a mutable read).
func globalRead() int {
	return g + wit(1)
}

// E1a: v := mut() + g, g written by the call. {1, 2}.
func e1read() int {
	mut := func() int { g = 2; return 0 }
	v := mut() + g
	return v
}

// E1c: g += setG() with setG writing g — the read occurrence + the store in then. {2, 11}.
func e1compound() int {
	g += setG()
	return g
}

// g = f(): a plain global target has no operands and the sweep no non-event → legacy.
func e1plainTarget() int {
	g = wit(1)
	return g
}

// BUG-113's c01: sinkL(left || b, change()) with left a PACKAGE variable — admitted now.
func bug113or() int {
	b := false
	change := func() int { b = true; return 0 }
	sinkL(left || b, change())
	return 1
}

// BUG-113's control: the call lexically first.
func bug113control() int {
	b := false
	change := func() int { b = true; return 0 }
	sinkR(change(), left || b)
	return 1
}

// A global of a type outside the grammar (a float64 compound target) stays legacy by name.
func globalTypeOut() {
	gf += float64(wit(1))
}

// --- Stage E E2: pointers, fields, maps ---

type P struct {
	f int
	n *P
}

func setVia(p *int) int { *p = 2; return 0 }

// E2a: *p + setVia(p) — the dereference is ONE read occurrence beside the call. {1, 2}.
func e2deref() int {
	x := 1
	p := &x
	return *p + setVia(p)
}

// E2b: q.f + setF(q) — a field read through a pointer. {1, 2}.
func setF(q *P) int { q.f = 2; return 0 }
func e2field() int {
	q := &P{f: 1}
	return q.f + setF(q)
}

// A field read on a PRIVATE struct variable beside a call that cannot touch it: no non-event → legacy.
func e2fieldPrivate() int {
	var s P
	s.f = 1
	return s.f + wit(1)
}

// A field read on an ADDRESS-TAKEN struct variable: the fused read is the occurrence.
func e2fieldAddrTaken() int {
	var s P
	mut := func() int { s.f = 2; return 0 }
	return s.f + mut()
}

// E2c: m[1] + setM(m) — a map element read. {1, 2}.
func setM(m map[int]int) int { m[1] = 2; return 0 }
func e2mapread() int {
	m := map[int]int{1: 1}
	return m[1] + setM(m)
}

// E2e: *p += redirect() — the plan freezes the pointer VALUE (mut redirects p).
func e2derefCompound() int {
	x, y := 10, 100
	p := &x
	mut := func() int { p = &y; return 1 }
	*p += mut()
	return x*1000 + y
}

// E2h: q.f += redirectQ() — a field compound target through a pointer.
func e2fieldCompound() int {
	a, b := &P{f: 10}, &P{f: 100}
	q := a
	mut := func() int { q = b; return 1 }
	q.f += mut()
	return a.f*1000 + b.f
}

// E2f: m[1] += rebind() — the plan freezes the map VALUE (mut rebinds m).
func e2mapCompound() int {
	m, m2 := map[int]int{1: 10}, map[int]int{1: 100}
	mut := func() int { m = m2; return 1 }
	m[1] += mut()
	return 0
}

// A map assign with a computed key beside a call: the key's checked access is the occurrence.
func e2mapAssignKey() int {
	m := map[int]int{}
	t := []int{1}
	k := 0
	m[t[k]] = wit(5)
	return len(m)
}

// A map assign on private atoms beside a call: no non-event (the plan checks nothing) → legacy.
func e2mapAssignPlain() int {
	m := map[int]int{}
	m[1] = wit(5)
	return len(m)
}

// A promoted field selector stays legacy by name.
type Outer struct{ P }
func e2promoted() int {
	o := &Outer{}
	return o.f + wit(1)
}

// An interface-keyed map stays legacy by name (the boxed key would sit inside the graph).
func e2ifaceKey() int {
	m := map[interface{}]int{}
	return m[1] + wit(1)
}

// A field target on a nested value base stays legacy by name.
func e2nestedFieldTarget() int {
	ss := []P{{}}
	ss[0].f = wit(1)
	return ss[0].f
}

// --- Stage E E3: receives and method calls ---

type V struct{ n int }

func (v V) Get() int   { return v.n }
func (v *V) Bump() int { v.n++; return v.n }

type I interface{ Get() int }

// E3a: a receive beside a read of an address-taken local: the receive is the event.
func e3recvRead() int {
	ch := make(chan int, 1)
	ch <- 1
	x := 1
	mut := func() int { x = 2; return 0 }
	_ = mut
	return <-ch + x + mut()
}

// E3b: a pointer-receiver method call on a pointer operand beside a read it mutates.
func e3ptrMethod() int {
	v := &V{n: 1}
	return v.n + v.Bump()
}

// E3c: a pointer-receiver call on an addressable variable (the implicit &v: a frozen ref).
func e3addrRecv() int {
	var v V
	s := []int{1}
	k := 0
	return s[k] + v.Bump()
}

// E3d: a value-receiver call through a pointer (the auto-deref is an occurrence).
func e3valueViaPtr() int {
	v := &V{n: 1}
	return v.Get() + wit(1)
}

// E3e: (*p).M() — the nil-asserting address of the dereference.
func e3starRecv() int {
	v := &V{n: 1}
	s := []int{1}
	k := 0
	return s[k] + (*v).Bump()
}

// An interface method call stays legacy by name (dynamic dispatch).
func e3ifaceMethod() int {
	var i I = V{n: 1}
	s := []int{1}
	return s[0] + i.Get()
}

// A comma-ok receive stays legacy by name (E5).
func e3commaOk() int {
	ch := make(chan int, 1)
	ch <- 1
	s := []int{1}
	v, ok := <-ch
	_ = ok
	return s[0] + v
}

// A promoted method stays legacy by name.
type W struct{ V }
func e3promotedMethod() int {
	w := &W{}
	s := []int{1}
	return s[0] + w.Bump()
}

// --- Stage E E4: conversions and allocations ---

func sinkAny(a any) int { _ = a; return 0 }

// E4a: int([]byte(s)[0]) + mut(), s captured (mut: s = "zz"): the read of s beside the call;
// the conversion and the index are pure ops on the fresh bytes.
func e4convRead() int {
	s := "ab"
	mut := func() int { s = "zz"; return 1 }
	return int([]byte(s)[0]) + mut()
}

// E4b: (&T{x: s[i]}).x + wit(5) — the payload read beside the call; the literal an allocate body.
func e4addrLit() int {
	s := []int{1}
	i := 0
	return (&T{x: s[i]}).x + wit(5)
}

// E4c: []int{s[i]}[0] + wit(5) — a slice literal's payload beside the call.
func e4sliceLit() int {
	s := []int{1}
	i := 0
	return []int{s[i]}[0] + wit(5)
}

// E4d: len(make([]int, t[k])) + x + mut(): make is an E1 participant (a function call), so
// t[k] inside its operand is FORCED before mut; the sweep enters through the captured x's read,
// unordered against mut. (Without x the sweep is all-forced and stays legacy — e4makeForced.)
func e4make() int {
	t := []int{1}
	k := 0
	x := 1
	mut := func() int { x = 2; return 0 }
	return len(make([]int, t[k])) + x + mut()
}

func e4makeForced() int {
	t := []int{1}
	k := 0
	return len(make([]int, t[k])) + wit(5)
}

// A VALUE struct literal beside a call: a pure struct-lit head over the payload.
func e4valueLit() int {
	s := []int{1}
	i := 0
	return T{x: s[i]}.x + wit(5)
}

// A map literal stays legacy by name (E5).
func e4mapLit() int {
	s := []int{1}
	return map[int]int{s[0]: 1}[0] + wit(5)
}

// A conversion to an interface type stays legacy by name (a box).
func e4ifaceConv() int {
	s := []int{1}
	return sinkAny(any(s[0])) + wit(5)
}

func conversionOperand() int {
	s := []int{1}
	return int(int64(s[0])) + wit(1)
}

func multiTarget() int {
	s := []int{1}
	var a, b int
	a, b = s[0], wit(1)
	return a + b
}

func lenOnly() int {
	s := []int{1, 2}
	return len(s)*10 + s[0]
}

func callOnly() int {
	s := []int{1}
	x := s[0]
	return wit(x) + wit(2)
}

func privateCompoundCall() int {
	out := 0
	out += wit(1)
	return out
}

func variadicCallee() int {
	s := []int{1}
	return s[0] + va(1, 2)
}

func genericCallee() int {
	s := []int{1}
	return s[0] + gen(1)
}

func stringIndex() int {
	str := "ab"
	return int(str[0]) + wit(1)
}

func arrayIndex() int {
	var arr [2]int
	return arr[0] + wit(1)
}

func ifaceCompare() bool {
	var a, b interface{} = 1, 2
	return a == b && wit(1) == 1
}

func floatOperand() float64 {
	f := 1.5
	return f + float64(wit(1))
}

func blankTarget() {
	s := []int{1}
	_ = s[0] + wit(1)
}

func namedTypeLocal() int {
	type N int
	var n N = 1
	return int(n) + wit(1)
}

func liftedBodyReadsCapture() int {
	x := 1
	f := func() int { return x + wit(1) }
	return f()
}

func printIface() {
	var iv interface{} = 1
	s := []int{1}
	println(s[0]+wit(1), iv)
}
`

func TestUnseqAdmittedWitnesses(t *testing.T) {
	cases := []struct {
		fn               string
		fromEnd          int
		form             string
		calls, nonEvents int
	}{
		{"w1", 1, "define", 1, 1},
		{"w6", 0, "return", 2, 1},
		{"r1", 0, "return", 1, 2},
		{"r6", 0, "return", 1, 2},   // header read of the captured a + the checked access
		{"w2", 0, "return", 1, 4},   // two captured headers (a, b) + two checked accesses (b[0], a[$b0])
		{"w3", 0, "compound", 1, 2}, // the element target plan + the read of the captured i
		{"r4", 1, "compound", 1, 2}, // the target plan + the header read of the captured a
		{"r2a", 0, "call-stmt", 3, 1},
		{"r2b", 0, "call-stmt", 2, 2},  // the guard + the read of the captured b
		{"r2c", 0, "call-stmt", 5, 3},  // gg, h, k, b2i, sink | the read of the captured a + two guards
		{"bug101a", 0, "return", 1, 3}, // the func literal is the ONE call; len is an event; iv read, assertion, slice expr
		{"bug101b", 0, "return", 1, 4}, // i read, slice, checked access, slice
		{"bug104a", 1, "compound", 2, 1},
		{"bug102", 1, "compound", 2, 2}, // calls fnine, wit (len is the third EVENT) | the target plan, b[j]
		{"retTwo", 0, "return", 1, 0},   // two results in return position: in the grammar, but no non-event (legacy)
		// Stage E E1: package-level variables
		{"globalRead", 0, "return", 1, 1},    // the global read is a mutable READ occurrence
		{"e1read", 1, "define", 1, 1},        // v := mut() + g
		{"e1compound", 1, "compound", 1, 1},  // g += setG(): the load of g is the read occurrence
		{"e1plainTarget", 1, "assign", 1, 0}, // g = wit(1): no non-event → legacy
		{"bug113or", 1, "call-stmt", 2, 3},   // change, sinkL | the global read, the address-taken b's read, the guard
		{"bug113control", 1, "call-stmt", 2, 3},
		// Stage E E2: pointers, fields, maps
		{"e2deref", 0, "return", 1, 1},              // *p: the dereference
		{"e2field", 0, "return", 1, 1},              // q.f through a pointer
		{"e2fieldPrivate", 0, "return", 1, 0},       // s.f on a private struct: a stable read → legacy
		{"e2fieldAddrTaken", 0, "return", 1, 1},     // the fused read of the address-taken s
		{"e2mapread", 0, "return", 1, 1},            // m[1]: the map read
		{"e2derefCompound", 1, "compound", 1, 2},    // the plan on the address-taken p's read + the load
		{"e2fieldCompound", 1, "compound", 1, 2},    // the plan on the address-taken q's read + the load
		{"e2mapCompound", 1, "compound", 1, 2},      // the plan on the address-taken m's read + the load
		{"e2mapAssignKey", 1, "map-assign", 1, 1},   // the key's checked access
		{"e2mapAssignPlain", 1, "map-assign", 1, 0}, // atoms only → legacy
		{"mapTarget", 1, "compound", 1, 2},          // BUG-104's m[t[k]] += wit(5): the key's checked access + the load
		{"derefRead", 0, "return", 1, 1},
		// Stage E E3: receives and method calls
		{"recvOperand", 1, "compound", 2, 1}, // BUG-104's x[fnine()] += <-ch: fnine + the receive | the target plan
		{"methodCall", 0, "return", 1, 1},    // s[0] + q.M(): the pointer-receiver call | the checked access
		{"e3recvRead", 0, "return", 2, 1},    // the receive + mut | the address-taken x
		{"e3ptrMethod", 0, "return", 1, 1},   // v.Bump() | the field read v.n through the pointer
		{"e3addrRecv", 0, "return", 1, 1},    // v.Bump() on &v (no read) | s[k]
		{"e3starRecv", 0, "return", 1, 2},    // (*v).Bump() | s[k] + the nil-asserting &*v
		// Stage E E4: conversions and allocations
		{"e4convRead", 0, "return", 1, 2},        // mut | the read of the captured s + the checked [0] on the bytes
		{"e4addrLit", 0, "return", 1, 2},         // wit | s[i] + the field read through the fresh pointer
		{"e4sliceLit", 0, "return", 1, 2},        // wit | s[i] + the checked [0] on the literal
		{"e4make", 0, "return", 1, 2},            // mut | t[k] (inside make — forced) + the captured x (observable)
		{"e4valueLit", 0, "return", 1, 1},        // wit | s[i] (the struct-lit and the field read on a value are pure)
		{"conversionOperand", 0, "return", 1, 1}, // int(int64(s[0])) + wit(1): the checked access; the conversions pure
	}
	for _, c := range cases {
		d := decisionAt(t, unseqWitnessSrc, c.fn, c.fromEnd)
		if d.form != c.form {
			t.Errorf("%s: form %q, want %q", c.fn, d.form, c.form)
		}
		if d.calls != c.calls || d.nonEvents != c.nonEvents {
			t.Errorf("%s: calls=%d nonEvents=%d, want %d/%d (reason %q)", c.fn, d.calls, d.nonEvents, c.calls, c.nonEvents, d.reason)
		}
		wantAdmitted := c.calls >= 1 && c.nonEvents >= 1
		if d.admitted != wantAdmitted {
			t.Errorf("%s: admitted=%v, want %v (reason %q)", c.fn, d.admitted, wantAdmitted, d.reason)
		}
		if wantAdmitted && d.reason != "" {
			t.Errorf("%s: admitted with a reason %q", c.fn, d.reason)
		}
	}
	// W5's sweep sits inside a for body: classify it directly.
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "main.go", unseqWitnessSrc, 0)
	if err != nil {
		t.Fatal(err)
	}
	info := newTypesInfo()
	pkg, err := (&types.Config{Importer: importer.Default()}).Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatal(err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	rows := []unseqCensusRow{}
	for _, d := range f.Decls {
		if fd, ok := d.(*ast.FuncDecl); ok && fd.Name.Name == "w5" {
			e.unseqCensus("w5", fd.Body, nil, nil, &rows)
		}
	}
	found := false
	for _, r := range rows {
		if r.dec.form == "print-stmt" {
			found = true
			// mut is the one call; the captured a's header read + the checked access
			if !r.dec.admitted || r.dec.calls != 1 || r.dec.nonEvents != 2 {
				t.Errorf("w5 println sweep: %+v", r.dec)
			}
		}
	}
	if !found {
		t.Errorf("w5: the loop body's println sweep was not censused")
	}
}

func TestUnseqLegacyByReason(t *testing.T) {
	cases := []struct {
		fn      string
		fromEnd int
		reason  string
	}{
		{"globalTypeOut", 0, "package-level target of a type outside the grammar"},
		{"e3ifaceMethod", 0, "interface method call"},
		// the E3 observability trigger: an occurrence forced before the only event beside it
		{"forcedArg", 0, "no occurrence observable against an effectful event"},
		{"e3valueViaPtr", 0, "no occurrence observable against an effectful event"}, // the auto-deref precedes Get, which precedes wit
		{"e3commaOk", 2, "multi-target or tuple assignment"},
		{"e3promotedMethod", 0, "promoted method call"},
		{"e2promoted", 0, "promoted field selector"},
		{"e2ifaceKey", 0, "map type outside the grammar"},
		{"e2nestedFieldTarget", 1, "field target on a non-variable struct base"},
		{"multiTarget", 1, "multi-target or tuple assignment"},
		{"lenOnly", 0, "no call occurrence"},
		{"callOnly", 0, "no non-event occurrence"},
		{"privateCompoundCall", 1, "no non-event occurrence"},
		{"variadicCallee", 0, "variadic callee"},
		{"genericCallee", 0, "generic function callee"},
		{"stringIndex", 0, "index of a non-slice base"}, // int(str[0]): the conversion is admitted (E4), the string index is not
		{"arrayIndex", 0, "index of a non-slice base"},
		{"ifaceCompare", 0, "interface comparison"},
		{"floatOperand", 0, "result type outside the pilot grammar"},
		{"blankTarget", 0, "blank target"},
		{"namedTypeLocal", 0, "conversion operand type outside the grammar"},
		{"printIface", 0, "print of an interface value"},
		// Stage E E4
		{"e4mapLit", 0, "map literal"},
		{"e4ifaceConv", 0, "conversion to an interface type"},
		{"e4makeForced", 0, "no occurrence observable against an effectful event"}, // t[k] precedes make, make precedes len, len precedes wit
	}
	for _, c := range cases {
		d := decisionAt(t, unseqWitnessSrc, c.fn, c.fromEnd)
		if d.admitted {
			t.Errorf("%s: admitted, want legacy (%s)", c.fn, c.reason)
			continue
		}
		if !strings.Contains(d.reason, c.reason) {
			t.Errorf("%s: reason %q does not name %q", c.fn, d.reason, c.reason)
		}
	}
	// A lifted body's read of its capture is a deref, outside the pilot: the
	// census passes the literal's free captures as `captured`.
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "main.go", unseqWitnessSrc, 0)
	if err != nil {
		t.Fatal(err)
	}
	info := newTypesInfo()
	pkg, err := (&types.Config{Importer: importer.Default()}).Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatal(err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	rows := []unseqCensusRow{}
	for _, d := range f.Decls {
		if fd, ok := d.(*ast.FuncDecl); ok && fd.Name.Name == "liftedBodyReadsCapture" {
			e.unseqCensus("liftedBodyReadsCapture", fd.Body, nil, nil, &rows)
		}
	}
	lit := 0
	for _, r := range rows {
		if strings.Contains(r.fn, "$lit") {
			lit++
			if r.dec.admitted || !strings.Contains(r.dec.reason, "captured variable read through its pointer parameter") {
				t.Errorf("lifted body sweep: %+v", r.dec)
			}
		}
	}
	if lit == 0 {
		t.Errorf("the func literal's body was not censused as its own unit")
	}
}

// The address-taken analysis: captured by a literal, `&x`, an array
// slicing, a method receiver; a plain local is private.
func TestUnseqAddrTaken(t *testing.T) {
	src := `package main
type T struct{ x int }
func (t *T) M() {}
func f() {
	a := 1
	b := 2
	c := [2]int{}
	var d T
	e := 5
	_ = func() int { return a }
	p := &b
	_ = c[:]
	d.M()
	_ = p
	_ = e
}
`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "main.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	info := newTypesInfo()
	pkg, err := (&types.Config{Importer: importer.Default()}).Check("main", fset, []*ast.File{file}, info)
	if err != nil {
		t.Fatal(err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	var body *ast.BlockStmt
	for _, d := range file.Decls {
		if fd, ok := d.(*ast.FuncDecl); ok && fd.Name.Name == "f" {
			body = fd.Body
		}
	}
	taken := e.unseqAddrTaken(body)
	byName := map[string]bool{}
	for obj := range taken {
		byName[obj.Name()] = true
	}
	for _, want := range []string{"a", "b", "c", "d"} {
		if !byName[want] {
			t.Errorf("%s should be address-taken", want)
		}
	}
	for _, private := range []string{"e", "p"} {
		if byName[private] {
			t.Errorf("%s should be private", private)
		}
	}
}
