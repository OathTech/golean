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
