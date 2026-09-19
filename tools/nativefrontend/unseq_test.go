package main

// Unit tests for the Stage C whole-sweep decision procedure (unseq.go,
// `unseqClassify`): the pilot grammar's admitted shapes — every reference
// witness the native pilot lowers (W1/W2/W3/W5/W6, R1/R2a-c/R4/R6, the
// BUG-101, BUG-104 and BUG-102 flip rows) — and the refusals BY REASON at
// the boundary (map targets, receives, methods, derefs, globals,
// conversions, multi-target forms, call-free and read-free sweeps). The
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

func globalRead() int {
	return g + wit(1)
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
		{"forcedArg", 0, "return", 1, 1},
		{"retTwo", 0, "return", 1, 0}, // two results in return position: in the grammar, but no non-event (legacy)
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
		{"mapTarget", 1, "element target on a non-slice base"},
		{"recvOperand", 1, "unary operator <-"},
		{"methodCall", 0, "callee expression outside the pilot grammar"},
		{"derefRead", 0, "pointer indirection"},
		{"globalRead", 0, "package-level variable"},
		{"conversionOperand", 0, "conversion"},
		{"multiTarget", 1, "multi-target or tuple assignment"},
		{"lenOnly", 0, "no call occurrence"},
		{"callOnly", 0, "no non-event occurrence"},
		{"privateCompoundCall", 1, "no non-event occurrence"},
		{"variadicCallee", 0, "variadic callee"},
		{"genericCallee", 0, "generic function callee"},
		{"stringIndex", 0, "conversion"}, // int(str[0]): the conversion is met first
		{"arrayIndex", 0, "index of a non-slice base"},
		{"ifaceCompare", 0, "interface comparison"},
		{"floatOperand", 0, "result type outside the pilot grammar"},
		{"blankTarget", 0, "blank target"},
		{"namedTypeLocal", 0, "conversion"},
		{"printIface", 0, "print of an interface value"},
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
