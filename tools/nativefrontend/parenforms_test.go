package main

// Unit pins for lane frontend/fix-paren-forms-1105 (2026-11-05): the UNPAREN
// RULE and the panic recovery recorded in emit.go's header. The differential
// rows (the S28 and S17 sweeps' Cases rows of BUG-420/421/422/390 and the
// lane's own packages) pin the observable contract — gc's values; these pin
// the WIRE SHAPES the differential cannot see: the blank target as `blank`
// (not an address), the parenthesised multi-value call splatted, the
// parenthesised range target bound, the fallthrough flag set past trailing
// empty statements, the parenthesised callee dispatched as the direct call
// (an atomic primitive, a sync op, a method, a lifted literal) and never as
// a func VALUE — and that an emission panic is the named whole-export
// refusal, never a crash.

import (
	"encoding/json"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

const parenFormsSrc = `package main

import (
	"sync"
	"sync/atomic"
)

var n int

func bump() int        { n++; return n }
func pair() (int, int) { return 3, 4 }
func add(a, b int) int { return a + b }

type pt struct{ x int }

func (p pt) get() int   { return p.x }
func (p *pt) inc() int  { p.x++; return p.x }

func blankSingle()     { (_) = bump() }
func blankMulti()      { x := 0; (_), x = bump(), 2; _ = x }
func blankMultiValue() { (_), (_) = pair() }
func blankCommaOk()    { m := map[string]int{}; var ok bool; (_), ok = m["a"]; _ = ok }
func blankRecv()       { ch := make(chan int, 1); var v int; (v), (_) = <-ch; _ = v }
func blankAssert()     { var i any = 1; var v int; (v), (_) = i.(int); _ = v }
func blankSelect() {
	ch := make(chan int, 1)
	select {
	case (_) = <-ch:
	}
}
func blankSelectPair() {
	ch := make(chan int, 1)
	var v int
	select {
	case (v), (_) = <-ch:
	}
	_ = v
}
func blankClosure() { f := func() { (_) = bump() }; f() }
func parenLocal() int  { x := 1; (x) = 2; (x)++; return x }
func parenCapture() int { x := 1; f := func() { (x) = 5 }; f(); return x }

func rangeParenKey() int      { s := []int{1}; var i int; for (i) = range s {}; return i }
func rangeParenBoth() int     { s := []int{1}; var i, v int; for (i), (v) = range s {}; return i + v }
func rangeParenBlankKey() int { s := []int{1}; var v int; for (_), (v) = range s {}; return v }

func mvDefine() int        { a, b := (pair()); return a + b }
func mvVar() int           { var c, d = (pair()); return c + d }
func mvAssign() int        { var c, d int; c, d = (pair()); return c + d }
func mvReturn() (int, int) { return (pair()) }
func mvSpread() int        { return add((pair())) }

func fallthroughThenEmpty(x int) int {
	r := 0
	switch x {
	case 1:
		r = 1
		fallthrough
		;
		;
	case 2:
		r += 10
	}
	return r
}

func fallthroughPlain(x int) int {
	r := 0
	switch x {
	case 1:
		r = 1
		fallthrough
	case 2:
		r += 10
	}
	return r
}

func emptiesNoFallthrough(x int) int {
	r := 0
	switch x {
	case 1:
		r = 1
		;
	case 2:
		r += 10
	}
	return r
}

func atomicParen() int32 { var x int32; (atomic.AddInt32)(&x, 1); return x }
func syncParen() int     { var mu sync.Mutex; (mu.Lock)(); defer (mu.Unlock)(); return 1 }
func wgParen() {
	var wg sync.WaitGroup
	(wg.Add)(1)
	go func() { defer (wg.Done)() }()
	(wg.Wait)()
}
func methodParen() int { p := pt{1}; return (p.get)() + (p.inc)() }
func litParen() int    { return (func(a int) int { return a * 2 })(4) }

func main() {}
`

// parenFormsProgram emits parenFormsSrc once per test that needs it.
func parenFormsProgram(t *testing.T) map[string]any {
	t.Helper()
	program, err := emitSource(t, parenFormsSrc)
	if err != nil {
		t.Fatalf("export refused: %v", err)
	}
	return program
}

// wireJSON renders a wire function for substring checks.
func wireJSON(t *testing.T, v any) string {
	t.Helper()
	b, err := json.Marshal(v)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	return string(b)
}

// The parenthesised blank is the `blank` target on every assignment route
// (BUG-420): the plain, multi-target and multi-value assignments, the
// comma-ok map read / receive / assertion, the select clause, a lifted
// closure body. Before the fix each of these CRASHED the frontend (localID
// on a nil object through the address-taking path).
func TestParenthesisedBlankIsTheBlankTarget(t *testing.T) {
	program := parenFormsProgram(t)
	for _, fn := range []string{"blankSingle", "blankMulti", "blankMultiValue", "blankCommaOk", "blankRecv", "blankAssert", "blankSelect", "blankSelectPair"} {
		w := wireJSON(t, wireFunc(t, program, fn))
		if strings.Contains(w, `"target":"addr"`) || strings.Contains(w, `"expr":"addr`) {
			t.Errorf("%s: the parenthesised blank took the address path: %s", fn, w)
		}
	}
	// The plain forms carry the literal `blank` target.
	for _, fn := range []string{"blankSingle", "blankMulti", "blankMultiValue"} {
		if w := wireJSON(t, wireFunc(t, program, fn)); !strings.Contains(w, `{"target":"blank"}`) {
			t.Errorf("%s: no `blank` target on the wire: %s", fn, w)
		}
	}
	// The closure's body is a lifted function; it must be on the wire and not refused.
	lifted := false
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		ff, _ := f.(map[string]any)
		if name, _ := ff["name"].(string); strings.HasPrefix(name, "blankClosure$lit") {
			lifted = true
			if u, refused := ff["unsupported"]; refused {
				t.Errorf("lifted closure refused: %v", u)
			}
		}
	}
	if !lifted {
		t.Errorf("blankClosure's literal was not lifted onto the wire")
	}
}

// A parenthesised identifier target is the identifier's `var` write
// (go/types lhsVar reads the target through parentheses), not an addressed
// location; in a lifted body it is the capture pointer.
func TestParenthesisedIdentifierTargetIsTheVariable(t *testing.T) {
	program := parenFormsProgram(t)
	w := wireJSON(t, wireFunc(t, program, "parenLocal"))
	if strings.Contains(w, `"target":"addr"`) {
		t.Errorf("parenLocal: `(x) = 2` / `(x)++` took the address path: %s", w)
	}
	if strings.Count(w, `"target":"var"`) < 2 {
		t.Errorf("parenLocal: `(x) = 2` and `(x)++` are not two `var` writes of x: %s", w)
	}
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		ff, _ := f.(map[string]any)
		if name, _ := ff["name"].(string); strings.HasPrefix(name, "parenCapture$lit") {
			if lw := wireJSON(t, ff); !strings.Contains(lw, `"kind":"capture"`) && !strings.Contains(lw, `x$cap`) {
				t.Errorf("parenCapture's literal: `(x) = 5` does not write through the capture pointer: %s", lw)
			}
		}
	}
}

// The assign-form range binds a parenthesised identifier target as the
// identifier (BUG-421); the blank key stays unbound.
func TestParenthesisedRangeTargetBinds(t *testing.T) {
	program := parenFormsProgram(t)
	for _, fn := range []string{"rangeParenKey", "rangeParenBoth", "rangeParenBlankKey"} {
		w := wireJSON(t, wireFunc(t, program, fn))
		if !strings.Contains(w, `"stmt":"range"`) && !strings.Contains(w, `"stmt":"for"`) {
			t.Errorf("%s: no loop on the wire: %s", fn, w)
		}
	}
	if w := wireJSON(t, wireFunc(t, program, "rangeParenBoth")); !strings.Contains(w, `$rangeKey`) || !strings.Contains(w, `$rangeVal`) {
		t.Errorf("rangeParenBoth: the key and value temps are not bound to (i), (v): %s", w)
	}
}

// A parenthesised multi-value call is the multi-value call at every sink
// (BUG-422): the define, var and assignment forms carry the two-result call
// as their one right-hand side (two `resultTypes`), the return and the
// spread splat it into temps — never a single-value hoist of the tuple
// (which `emitType` refuses as a hoisted tuple).
func TestParenthesisedMultiValueCallIsTheCall(t *testing.T) {
	program := parenFormsProgram(t)
	for _, fn := range []string{"mvDefine", "mvVar", "mvAssign", "mvReturn", "mvSpread"} {
		w := wireJSON(t, wireFunc(t, program, fn))
		if !strings.Contains(w, `"expr":"call","func":"pair","resultTypes":[{"int":"int","kind":"int"},{"int":"int","kind":"int"}]`) {
			t.Errorf("%s: the parenthesised multi-value call is not the two-result call of pair: %s", fn, w)
		}
	}
	for _, fn := range []string{"mvReturn", "mvSpread"} {
		if w := wireJSON(t, wireFunc(t, program, fn)); strings.Count(w, `"target":"declare"`) < 2 {
			t.Errorf("%s: the tuple was not splatted into two temps: %s", fn, w)
		}
	}
}

// fallthroughFlags counts, in a function's wire, the assignments that set a
// switch's fallthrough variable (`$swfN`) to true — one per clause that
// falls through.
func fallthroughFlags(t *testing.T, fn map[string]any) int {
	t.Helper()
	count := 0
	var walk func(v any)
	walk = func(v any) {
		switch x := v.(type) {
		case map[string]any:
			if x["stmt"] == "assign" {
				lhs, _ := x["lhs"].([]any)
				rhs, _ := x["rhs"].([]any)
				if len(lhs) == 1 && len(rhs) == 1 {
					l, _ := lhs[0].(map[string]any)
					r, _ := rhs[0].(map[string]any)
					id, _ := l["id"].(string)
					if strings.HasPrefix(id, "$swf") && r["expr"] == "bool" && r["value"] == true {
						count++
					}
				}
			}
			for _, c := range x {
				walk(c)
			}
		case []any:
			for _, c := range x {
				walk(c)
			}
		}
	}
	walk(fn)
	return count
}

// A `fallthrough` followed by explicit empty statements is the clause's
// final non-empty statement (BUG-390; go/types trimTrailingEmptyStmts): the
// clause falls through exactly as the plain spelling does, and a clause
// whose trailing empty statement follows an ordinary statement does not.
func TestFallthroughPastTrailingEmptyStatements(t *testing.T) {
	program := parenFormsProgram(t)
	if got := fallthroughFlags(t, wireFunc(t, program, "fallthroughThenEmpty")); got != 1 {
		t.Errorf("fallthroughThenEmpty: %d fallthrough flags set, want 1", got)
	}
	if got := fallthroughFlags(t, wireFunc(t, program, "fallthroughPlain")); got != 1 {
		t.Errorf("fallthroughPlain: %d fallthrough flags set, want 1", got)
	}
	if got := fallthroughFlags(t, wireFunc(t, program, "emptiesNoFallthrough")); got != 0 {
		t.Errorf("emptiesNoFallthrough: %d fallthrough flags set, want 0", got)
	}
}

// A parenthesised callee is the callee it names (go/types callExpr reads
// call.Fun through its paren arm): the sync/atomic primitives take their
// fused ops, a method call is the direct method call, an immediately
// invoked literal is the lifted literal's call — none a `call-value`
// through a func value, none a refusal.
func TestParenthesisedCalleeIsTheDirectCall(t *testing.T) {
	program := parenFormsProgram(t)
	if w := wireJSON(t, wireFunc(t, program, "atomicParen")); !strings.Contains(w, `"atomic-op"`) || strings.Contains(w, `call-value`) {
		t.Errorf("atomicParen: `(atomic.AddInt32)(&x, 1)` is not the fused atomic-op: %s", w)
	}
	if w := wireJSON(t, wireFunc(t, program, "syncParen")); !strings.Contains(w, `"op":"lock","stmt":"sync-op"`) || !strings.Contains(w, `$deferSync`) || strings.Contains(w, `call-value`) {
		t.Errorf("syncParen: `(mu.Lock)()` is not the lock op or `defer (mu.Unlock)()` is not the deferred sync closer: %s", w)
	}
	if w := wireJSON(t, wireFunc(t, program, "wgParen")); strings.Count(w, `"stmt":"sync-op"`) < 2 || strings.Contains(w, `call-value`) {
		t.Errorf("wgParen: `(wg.Add)(1)` / `(wg.Wait)()` are not the sync ops: %s", w)
	}
	if w := wireJSON(t, wireFunc(t, program, "methodParen")); strings.Contains(w, `call-value`) || strings.Count(w, `"expr":"call"`) < 2 {
		t.Errorf("methodParen: `(p.get)()` / `(p.inc)()` are not direct method calls: %s", w)
	}
	if w := wireJSON(t, wireFunc(t, program, "litParen")); !strings.Contains(w, `$lit`) {
		t.Errorf("litParen: `(func(a int) int {…})(4)` does not call the lifted literal: %s", w)
	}
}

// emitSourceRecovering is emitSource through the frontend's top-level entry
// (emitProgramRecovering), the way run() enters emission.
func emitSourceRecovering(t *testing.T, src string) (map[string]any, error) {
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
	return e.emitProgramRecovering([]*ast.File{f})
}

// A panic raised anywhere in emission is the named whole-export refusal
// `native frontend internal error: …` — the panic value, the declaration in
// progress and the raising frame named — and no program is returned. The
// panic is injected through emitPanicHook (the test seam; nil in production).
func TestEmissionPanicIsANamedRefusal(t *testing.T) {
	emitPanicHook = func() { panic("injected emission panic") }
	defer func() { emitPanicHook = nil }()
	program, err := emitSourceRecovering(t, "package main\nfunc main() {}\n")
	if err == nil {
		t.Fatal("an emission panic produced a program instead of a refusal")
	}
	if program != nil {
		t.Errorf("an emission panic returned a program beside the refusal: %v", program)
	}
	msg := err.Error()
	if !strings.HasPrefix(msg, "native frontend internal error: injected emission panic") {
		t.Errorf("the refusal does not name the panic: %q", msg)
	}
	if !strings.Contains(msg, "while emitting ") || !strings.Contains(msg, " at ") || !strings.Contains(msg, "(parenforms_test.go:") {
		t.Errorf("the refusal does not name the declaration and the raising frame: %q", msg)
	}
	if _, isUnsup := err.(unsupported); isUnsup {
		t.Errorf("an internal error must not be an `unsupported` (quarantinable) refusal: %q", msg)
	}
}

// Without the hook the same entry emits the program (the recovery is inert
// on the happy path).
func TestEmissionRecoveryIsInertWithoutAPanic(t *testing.T) {
	program, err := emitSourceRecovering(t, "package main\nfunc f() int { return 1 }\nfunc main() {}\n")
	if err != nil {
		t.Fatalf("export refused: %v", err)
	}
	wireFunc(t, program, "f")
}

// localID on a reference with no go/types object panics BY NAME (the
// invariant BUG-420 broke silently): the recovery then carries the name.
func TestLocalIDWithoutObjectPanicsByName(t *testing.T) {
	e := &emitter{}
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("localID(nil) returned instead of panicking")
		}
		if s, _ := r.(string); !strings.Contains(s, "localID: no go/types object for the capture reference \"x\"") {
			t.Errorf("localID(nil) panicked without naming the invariant: %v", r)
		}
	}()
	e.localID(nil, "capture", "x")
}
