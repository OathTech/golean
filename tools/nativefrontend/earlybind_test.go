package main

// The legacy ANF hoist's EARLY-BINDING rule and LATE suffix after the fix
// lane frontend/fix-unseq-seam-1027 (2026-10-27): BUG-310 (a type assertion
// to a non-pointer-shaped type, a slice expression and a string slice bind
// to a temp at their lexical position when an ordered event follows them,
// in every sweep the unseq grammar declines), BUG-313 (the `[]byte(s)` /
// `[]rune(s)` conversion binds there whatever its operand carries) and
// BUG-311 (an interface method value's box and a slice literal / `&T{…}`
// bind AFTER the sweep's events, where gc builds them; a method value boxed
// into an interface binds early). The differential rows under
// Corpus/coverage/exec/evalorder/sweep-s8-{early-kinds-legacy,method-values,
// conv-probed-operand} pin the observations; these pin the WIRE SHAPES the
// observations rest on, so a regression names its statement.

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

const earlyBindSrc = `package main

type MyInt int

type T2 struct{ n int }

func (t T2) M() int { return t.n }

type I2 interface{ M() int }

type PT struct{ n int }

func (p *PT) PM() int { return p.n }

var arr = [2]int{0, 0} // an array operand or target declines the unseq grammar
var iv any = 1
var s = []int{1, 5}
var str = "ab"
var ps = &str
var j = 1
var i2 I2 = T2{1}
var v = T2{1}

func set() int { iv = 5; j = 9; str = "zz"; v.n = 5; i2 = T2{5}; return 10 }
func sink(a, b int) int { return a*100 + b }
func sinkF(f func() int, k int) int { return f()*100 + k }
func sinkS(xs []int, k int) int { return xs[0]*100 + k }
func sinkP(p *PT, k int) int { return p.n*100 + k }

type P2 struct{ a, b int }
type PS struct{ s []int }

func sinkAny(a any, k int) int { return k }
func sinkSA(xs []int, a any, k int) int { return xs[0]*100 + k }
func sinkFA(f func() int, a any, k int) int { return f() + k }

// BUG-310: the early kinds at sweeps the grammar declines.
func assertIfCond() int {
	if iv.(int) > set() {
		return 1
	}
	return 0
}
func assertVarSpec() int { var x = iv.(int) + set(); return x }
func assertDefer()       { defer sink(iv.(int), set()) }
func assertGo()          { go sink(iv.(int), set()) }
func assertArrayOperand() int { return arr[0] + iv.(int) + set() }
func assertArrayTarget()      { arr[iv.(int)] = set() }
func sliceExprVarSpec() int   { var x = s[j:][0] + set(); return x }
func stringSliceVarSpec() int { var x = int(str[1:][0]) + set(); return x }

// No later event: the inline form, byte-identical to before.
func assertNoLaterEvent() int { n := set(); return arr[0] + iv.(int) + n }

// A pointer-shaped target: gc leaves the assertion in the residual.
func assertPointerShaped() int { var x = sinkP(iv.(*PT), set()); return x }

// The narrowed A6 guard sees the bound assertion as covered.
func guardCovered() int { return arr[0] + iv.(int) + len(s[j:]) + set() }

// BUG-313: the conversion of a PROBED operand binds at its position.
func bytesDerefArr() int    { return int([]byte(*ps)[0]) + arr[0] + set() }
func bytesDefined() MyInt   { return MyInt([]byte(*ps)[0]) + MyInt(set()) }

// BUG-311: the method value's receiver at gc's point per form.
func mvIfaceArg() int                { return sinkF(i2.M, set()) }
func mvIfaceTuple() (func() int, int) { f, k := i2.M, set(); return f, k }
func mvValueAnySlice() int           { l := []any{v.M, set()}; return len(l) }
func mvIfaceAnySlice() int           { l := []any{i2.M, set()}; return len(l) }
func mvFuncSliceIndexed() int        { mv := []func() int{v.M, nil}[set()-10]; return mv() }
func mvMapLit() int                  { m := map[int]any{1: v.M, 2: set()}; return len(m) }
func mvIfaceNoLaterEvent() int       { n := set(); return sinkF(i2.M, n) }

// The structural allocations gc builds in walk: a lifted body reading a
// captured local through its pointer parameter declines the grammar.
func sliceLitClosure() int {
	w := T2{1}
	setW := func() int { w.n = 5; return 10 }
	fn := func() int { return sinkS([]int{w.n}, setW()) }
	return fn()
}
func ptrLitClosure() int {
	w := T2{1}
	setW := func() int { w.n = 5; return 10 }
	fn := func() int { return sinkP(&PT{w.n}, setW()) }
	return fn()
}

// The train-31 audit's finding A: a late entry is promoted with its own
// dependencies only — an unrelated late allocation stays after the sweep's
// events (lifted bodies decline the grammar).
func lateSliceThenBox() int {
	w := T2{1}
	setW := func() int { w.n = 5; return 10 }
	fn := func() int { return sinkSA([]int{w.n}, i2.M, setW()) }
	return fn()
}
func lateTwoMethodValues() int {
	setI := func() int { i2 = T2{5}; return 10 }
	fn := func() int { return sinkFA(i2.M, i2.M, setI()) }
	return fn()
}
func lateReadsLate() int {
	w := T2{1}
	setW := func() int { w.n = 5; return 10 }
	fn := func() int { return sinkAny(&PS{s: []int{w.n}}, setW()) }
	return fn()
}

// The train-31 audit's finding B: a NON-ADDRESSABLE operand of a needsaddr
// kind boxed into an interface binds at its position (var specs decline
// the grammar); an addressable one and a by-value kind stay inline.
func boxStructLit() int  { var x = sinkAny(P2{v.n, 0}, set()); return x }
func boxArrayLit() int   { var x = sinkAny([2]int{v.n, 0}, set()); return x }
func boxPtrLit() int     { var x = sinkAny(&P2{v.n, 0}, set()); return x }
func boxComparison() int { var x = sinkAny(v.n > 0, set()); return x }
func boxConvInt8() int   { var x = sinkAny(int8(v.n), set()); return x }
func boxVariable() int   { var x = sinkAny(v, set()); return x }
func boxIntArith() int   { var x = sinkAny(v.n+0, set()); return x }
func boxOneFieldLit() int { var x = sinkAny(T2{v.n}, set()); return x }
func boxSliceLit() int   { var x = sinkAny([]int{v.n}, set()); return x }

func main() {}
`

func earlyBindProgram(t *testing.T) map[string]any {
	t.Helper()
	program, err := emitSource(t, earlyBindSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	return program
}

// declIndex is the index of the first top-level statement of fn that
// declares a temp with the given prefix (`$mv`, `$c`), or -1.
func declIndex(fn map[string]any, prefix string) int {
	body, _ := fn["body"].(map[string]any)
	stmts, _ := body["body"].([]any)
	for i, st := range stmts {
		if strings.HasPrefix(declaredTemp(st), prefix) {
			return i
		}
	}
	return -1
}

// nthHead is the index of the n-th (0-based) occurrence of head, or -1.
func nthHead(heads []string, want string, n int) int {
	for i, h := range heads {
		if h == want {
			if n == 0 {
				return i
			}
			n--
		}
	}
	return -1
}

func TestEarlyKindsBindBeforeLaterEvent(t *testing.T) {
	program := earlyBindProgram(t)
	for fn, head := range map[string]string{
		"assertIfCond":       "assign:type-assert",
		"assertVarSpec":      "assign:type-assert",
		"assertDefer":        "assign:type-assert",
		"assertGo":           "assign:type-assert",
		"assertArrayOperand": "assign:type-assert",
		"assertArrayTarget":  "assign:type-assert",
		"sliceExprVarSpec":   "assign:slice",
		"stringSliceVarSpec": "assign:slice",
		"bytesDerefArr":      "assign:bytes-from-string",
		"bytesDefined":       "assign:bytes-from-string",
		"guardCovered":       "assign:type-assert",
	} {
		heads := bodyHeads(wireFunc(t, program, fn))
		early := indexOfHead(heads, head)
		call := indexOfHead(heads, "assign:call")
		if early < 0 || call < 0 || early >= call {
			t.Errorf("%s: the %s temp must precede the set() temp; body heads %v", fn, head, heads)
		}
		if n := unseqCount(t, program, fn); n != 0 {
			t.Errorf("%s: expected the legacy path, got %d unseq graph(s)", fn, n)
		}
	}
	// The probed operand's probe (the dereference's) is dropped: the bound
	// conversion evaluates it. The sibling `arr[0]` and the index of the
	// converted temp keep theirs.
	for _, fn := range []string{"bytesDerefArr", "bytesDefined"} {
		body, _ := wireFunc(t, program, fn)["body"].(map[string]any)
		for _, st := range body["body"].([]any) {
			if isProbeStmt(st) {
				if x, _ := st.(map[string]any)["expr"].(map[string]any); x["expr"] == "deref" {
					t.Errorf("%s: the bound conversion's dereference operand must carry no probe", fn)
				}
			}
		}
	}
	// No later event, or a pointer-shaped target: inline, no temp.
	for _, fn := range []string{"assertNoLaterEvent", "assertPointerShaped"} {
		heads := bodyHeads(wireFunc(t, program, fn))
		if indexOfHead(heads, "assign:type-assert") >= 0 {
			t.Errorf("%s: the assertion must stay inline; body heads %v", fn, heads)
		}
	}
}

func TestMethodValueBindsAtGcsPoint(t *testing.T) {
	program := earlyBindProgram(t)
	// An interface method value beside a later call: the box binds after
	// the call's temp and before the consuming call's temp.
	heads := bodyHeads(wireFunc(t, program, "mvIfaceArg"))
	mv := declIndex(wireFunc(t, program, "mvIfaceArg"), "$mv")
	if set, consumer := nthHead(heads, "assign:call", 0), nthHead(heads, "assign:call", 1); mv < 0 || set < 0 || consumer < 0 || !(set < mv && mv < consumer) {
		t.Errorf("mvIfaceArg: the $mv binding must sit after set()'s temp and before sinkF's; $mv at %d, body heads %v", mv, heads)
	}
	heads = bodyHeads(wireFunc(t, program, "mvIfaceTuple"))
	if mv, set := declIndex(wireFunc(t, program, "mvIfaceTuple"), "$mv"), indexOfHead(heads, "assign:call"); mv < 0 || set < 0 || mv < set {
		t.Errorf("mvIfaceTuple: the $mv binding must follow set()'s temp; $mv at %d, body heads %v", mv, heads)
	}
	// No later event: the box binds at its position, before the consumer.
	heads = bodyHeads(wireFunc(t, program, "mvIfaceNoLaterEvent"))
	if mv, consumer := declIndex(wireFunc(t, program, "mvIfaceNoLaterEvent"), "$mv"), nthHead(heads, "assign:call", 1); mv < 0 || consumer < 0 || mv > consumer {
		t.Errorf("mvIfaceNoLaterEvent: the $mv binding must precede sinkF's temp; $mv at %d, body heads %v", mv, heads)
	}
	// A method value boxed into `any`: the box binds early, before the call.
	for _, fn := range []string{"mvValueAnySlice", "mvIfaceAnySlice"} {
		heads := bodyHeads(wireFunc(t, program, fn))
		box, call := indexOfHead(heads, "assign:to-interface"), indexOfHead(heads, "assign:call")
		if box < 0 || call < 0 || box >= call {
			t.Errorf("%s: the boxed method value's temp must precede set()'s; body heads %v", fn, heads)
		}
	}
	if mv, box := declIndex(wireFunc(t, program, "mvIfaceAnySlice"), "$mv"), indexOfHead(bodyHeads(wireFunc(t, program, "mvIfaceAnySlice")), "assign:to-interface"); mv < 0 || mv > box {
		t.Errorf("mvIfaceAnySlice: the $mv binding must precede the box that captures it; $mv at %d, box at %d", mv, box)
	}
	// The map literal keeps its entries at the literal: no early box.
	heads = bodyHeads(wireFunc(t, program, "mvMapLit"))
	if indexOfHead(heads, "assign:to-interface") >= 0 || indexOfHead(heads, "map-lit") < indexOfHead(heads, "assign:call") {
		t.Errorf("mvMapLit: the map literal's boxed entry stays in the literal, after the call temp; body heads %v", heads)
	}
}

func TestStructuralAllocationBindsAfterLaterEvent(t *testing.T) {
	program := earlyBindProgram(t)
	heads := bodyHeads(wireFunc(t, program, "mvFuncSliceIndexed"))
	if lit, call := indexOfHead(heads, "slice-lit"), indexOfHead(heads, "assign:call"); lit < 0 || call < 0 || lit < call {
		t.Errorf("mvFuncSliceIndexed: the slice literal must follow set()'s temp; body heads %v", heads)
	}
	for fn, head := range map[string]string{"sliceLitClosure$lit1": "slice-lit", "ptrLitClosure$lit1": "new"} {
		heads := bodyHeads(wireFunc(t, program, fn))
		lit := indexOfHead(heads, head)
		set, consumer := indexOfHead(heads, "assign:call-value"), indexOfHead(heads, "assign:call")
		if lit < 0 || set < 0 || consumer < 0 || !(set < lit && lit < consumer) {
			t.Errorf("%s: the %s must sit after set()'s temp and before the consuming call's; body heads %v", fn, head, heads)
		}
	}
}

// TestGcEarlyOperand pins the predicate over the operand kinds: an assertion
// to a non-pointer-shaped type, a slice expression (slice, string, array
// base) and the allocating string conversions answer true; an assertion to a
// pointer-shaped type (pointer, func, chan, map, a one-field struct or
// one-element array of such), an index, a dereference, a numeric conversion,
// `string(bs)` and a constant do not (a constant string's slice is not a
// constant: gc copies it like any slice expression).
func TestGcEarlyOperand(t *testing.T) {
	src := `package main

type MyInt int
type T2 struct{ n int }
type I2 interface{ M() int }
type PT struct{ n int }

var (
	iv  any
	s   []int
	str string
	arr [2]int
	bs  []byte
	ps  *string
	j   int
)

func probe() {
	_ = iv.(int)
	_ = iv.(T2)
	_ = iv.(I2)
	_ = iv.(string)
	_ = iv.([]int)
	_ = iv.(*PT)
	_ = iv.(func() int)
	_ = iv.(chan int)
	_ = iv.(map[int]int)
	_ = iv.(struct{ p *PT })
	_ = iv.([1]*PT)
	_ = s[1:]
	_ = str[1:]
	_ = arr[:]
	_ = []byte(str)
	_ = []rune(str)
	_ = string(bs)
	_ = s[j]
	_ = *ps
	_ = MyInt(j)
	_ = "abc"[1:]
}

func main() {}
`
	want := []bool{true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true}
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "probe.go", src, 0)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info := newTypesInfo()
	conf := types.Config{Importer: importer.Default()}
	pkg, err := conf.Check("main", fset, []*ast.File{file}, info)
	if err != nil {
		t.Fatalf("type-check: %v", err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	var stmts []ast.Stmt
	for _, d := range file.Decls {
		if fd, ok := d.(*ast.FuncDecl); ok && fd.Name.Name == "probe" {
			stmts = fd.Body.List
		}
	}
	if len(stmts) != len(want) {
		t.Fatalf("probe has %d statements, the table %d", len(stmts), len(want))
	}
	for i, st := range stmts {
		rhs := st.(*ast.AssignStmt).Rhs[0]
		if got := e.gcEarlyOperand(rhs); got != want[i] {
			t.Errorf("gcEarlyOperand(%s) = %v, want %v", src[fset.Position(rhs.Pos()).Offset:fset.Position(rhs.End()).Offset], got, want[i])
		}
	}
}

// TestLateEntriesPromoteByDependency pins the train-31 audit's finding A
// (lane frontend/fix-e7-cut-1107, 2026-11-07): `insertMain` promotes a late
// entry with the entries it reads and the ones pushed with it — nothing
// else. Before, every late entry up to the last one read was promoted, so
// `sinkS([]int{n}, j.M, set())` read n before set() (gc 500, the machine 0)
// and `sinkF2(i.M, j.M, set())` nil-checked i.M's box before set() assigned
// i (gc 1, the machine a nil-dereference panic).
func TestLateEntriesPromoteByDependency(t *testing.T) {
	program := earlyBindProgram(t)
	// A slice literal pushed late before the method value's box: the box's
	// early binding promotes the `$mv` group only; the slice literal stays
	// after set()'s temp.
	fn := wireFunc(t, program, "lateSliceThenBox$lit1")
	heads := bodyHeads(fn)
	set, lit, box := indexOfHead(heads, "assign:call-value"), indexOfHead(heads, "slice-lit"), indexOfHead(heads, "assign:to-interface")
	mv := declIndex(fn, "$mv")
	if set < 0 || lit < 0 || box < 0 || mv < 0 || !(mv < box && box < set && set < lit) {
		t.Errorf("lateSliceThenBox: want $mv < box < set() temp < slice literal; $mv %d box %d set %d lit %d, body heads %v", mv, box, set, lit, heads)
	}
	// Two interface method values, the second boxed: the second's binding
	// (and its nil check) precede set()'s temp, the first's follow it.
	fn = wireFunc(t, program, "lateTwoMethodValues$lit1")
	heads = bodyHeads(fn)
	body, _ := fn["body"].(map[string]any)
	stmts, _ := body["body"].([]any)
	var mvs []int
	for i, st := range stmts {
		if strings.HasPrefix(declaredTemp(st), "$mv") {
			mvs = append(mvs, i)
		}
	}
	set = indexOfHead(heads, "assign:call-value")
	box = indexOfHead(heads, "assign:to-interface")
	if len(mvs) != 2 || set < 0 || box < 0 || !(mvs[0] < box && box < set && set < mvs[1]) {
		t.Errorf("lateTwoMethodValues: want the boxed $mv < box < set() temp < the other $mv; $mv at %v box %d set %d, body heads %v", mvs, box, set, heads)
	}
	// A late `new` reading a late slice literal, boxed: both promoted, in order.
	fn = wireFunc(t, program, "lateReadsLate$lit1")
	heads = bodyHeads(fn)
	set, lit, nw, box := indexOfHead(heads, "assign:call-value"), indexOfHead(heads, "slice-lit"), indexOfHead(heads, "new"), indexOfHead(heads, "assign:to-interface")
	if set < 0 || lit < 0 || nw < 0 || box < 0 || !(lit < nw && nw < box && box < set) {
		t.Errorf("lateReadsLate: want slice literal < new < box < set() temp; lit %d new %d box %d set %d, body heads %v", lit, nw, box, set, heads)
	}
}

// TestNeedsAddrOperandBoxesEarly pins the train-31 audit's finding B (lane
// frontend/fix-e7-cut-1107): the boxed temp of a non-addressable needsaddr
// operand precedes set()'s temp; a by-value kind or an addressable operand
// keeps the inline box.
func TestNeedsAddrOperandBoxesEarly(t *testing.T) {
	program := earlyBindProgram(t)
	for _, fn := range []string{"boxStructLit", "boxArrayLit", "boxPtrLit", "boxComparison", "boxConvInt8"} {
		heads := bodyHeads(wireFunc(t, program, fn))
		box, call := indexOfHead(heads, "assign:to-interface"), indexOfHead(heads, "assign:call")
		if box < 0 || call < 0 || box >= call {
			t.Errorf("%s: the boxed operand's temp must precede set()'s; body heads %v", fn, heads)
		}
		if n := unseqCount(t, program, fn); n != 0 {
			t.Errorf("%s: expected the legacy path, got %d unseq graph(s)", fn, n)
		}
	}
	for _, fn := range []string{"boxVariable", "boxIntArith", "boxOneFieldLit", "boxSliceLit"} {
		heads := bodyHeads(wireFunc(t, program, fn))
		if indexOfHead(heads, "assign:to-interface") >= 0 {
			t.Errorf("%s: the box must stay inline (an addressable operand or a by-value kind); body heads %v", fn, heads)
		}
	}
}

// TestNeedsAddrForIface pins dataWordFuncName's port over the kinds: by
// value (false) for the 2/4/8-byte pointer-free kinds, a sole-component
// string or slice through one-field structs and one-element arrays; by
// address (true) for bool, int8, a two-field struct, `[2]int`, a pointer, a
// func, a chan, a map, a pointer-bearing struct, a 16-byte float pair — and
// a function-local type capturing the stencil's parameter is laid out at
// the instantiation (the crash the corpus comparison found on
// generics/sweep-s3-local-in-generic).
func TestNeedsAddrForIface(t *testing.T) {
	src := `package main

type P2 struct{ a, b int }
type Q1 struct{ a int }
type R struct{ p *int; k int }
type SS struct{ s string }
type SL struct{ s []int }
type A1 [1]string
type F2 struct{ x, y float64 }
type E struct{}
type Z struct{ a int; z struct{} }

var (
	b  bool
	i8 int8
	i16 int16
	i32 int32
	i  int
	u  uintptr
	f32 float32
	f64 float64
	s  string
	sl []int
	p2 P2
	q1 Q1
	r  R
	ss SS
	slw SL
	a1 A1
	a2 [2]int
	f2 F2
	e  E
	z  Z
	pp *int
	fn func()
	ch chan int
	m  map[int]int
)

func probe() {
	_ = b
	_ = i8
	_ = i16
	_ = i32
	_ = i
	_ = u
	_ = f32
	_ = f64
	_ = s
	_ = sl
	_ = p2
	_ = q1
	_ = r
	_ = ss
	_ = slw
	_ = a1
	_ = a2
	_ = f2
	_ = e
	_ = z
	_ = pp
	_ = fn
	_ = ch
	_ = m
}

func main() {}
`
	want := []bool{true, true, false, false, false, false, false, false, false, false, true, false, true, false, false, false, true, true, true, true, true, true, true, true}
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "probe.go", src, 0)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info := newTypesInfo()
	conf := types.Config{Importer: importer.Default()}
	pkg, err := conf.Check("main", fset, []*ast.File{file}, info)
	if err != nil {
		t.Fatalf("type-check: %v", err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	var stmts []ast.Stmt
	for _, d := range file.Decls {
		if fd, ok := d.(*ast.FuncDecl); ok && fd.Name.Name == "probe" {
			stmts = fd.Body.List
		}
	}
	if len(stmts) != len(want) {
		t.Fatalf("probe has %d statements, the table %d", len(stmts), len(want))
	}
	for i, st := range stmts {
		rhs := st.(*ast.AssignStmt).Rhs[0]
		if got := e.needsAddrForIface(info.TypeOf(rhs)); got != want[i] {
			t.Errorf("needsAddrForIface(%s: %s) = %v, want %v", src[fset.Position(rhs.Pos()).Offset:fset.Position(rhs.End()).Offset], info.TypeOf(rhs), got, want[i])
		}
	}
	// A function-local type capturing the generic's parameter: the layout
	// is the instantiation's (box[int] is one 8-byte field — by value;
	// box[string] a 16-byte string — by value too, its sole component; a
	// pair[int] two ints — by address).
	gsrc := `package main

func wrap[T any](x T) any {
	type box struct{ v T }
	type pair struct{ v, w T }
	return any(box{x}) == any(pair{x, x})
}

func main() { _ = wrap[int](1); _ = wrap[string]("a") }
`
	program, err := emitSource(t, gsrc)
	if err != nil {
		t.Fatalf("a local type capturing the stencil's parameter must lower: %v", err)
	}
	if program == nil {
		t.Fatal("no program")
	}
}
