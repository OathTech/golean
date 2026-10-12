package main

// The `type` key on expression nodes (release-readiness punch list item 2,
// 2026-10-12). The wire contract `emitExpr` keeps: every SINGLE-VALUED
// expression node it emits carries its go/types type under `type`; the two
// shapes without a single type — a tuple-typed call (multi-valued or no
// result; its consumers read `resultTypes`, BUG-110) and the bare `nil`
// literal (the decoder's `nil` arm takes an optional type) — omit it BY
// NAME (`noSingleWireType`, wire.go); and a `typeOf` failure is RETURNED as
// the declaration's refusal, never swallowed by dropping the key (before,
// the key was dropped silently and the decoder declared the temporary
// `int`, whatever value it held). The decoder READS the key at two consumer
// positions (`exprTypeOf`, GoLean/NativeToIR.lean): a blank assignment's
// rhs node (the discard temporary) and an indexable/channel range's
// collection node (the `$rcoll` temporary) — never a call-shaped node
// (routed through `resultTypes` first) and never the comma-ok `map-get`
// (routed through `asMapGet?` first). Nodes built OUTSIDE `emitExpr` — the
// expression-statement call, the comma-ok map read, the unseq graph's
// callee — carry no `type` and reach no consumer. The whole-corpus export
// comparison that fixed the carve-out list (1386 packages, old vs new
// frontend, 2026-10-12) found every wire byte-identical, and a scan of the
// 1361 exported wires found no consumer position without the key (the 30
// typeless `map-get` nodes are all comma-ok rhs).

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strconv"
	"strings"
	"testing"
)

// The shapes a lowering meets: literals, idents, operators, calls of every
// arity (0, 1, 2 results), conversions, composite literals, indexing,
// field/method selectors, closures, a `nil` assignment and a `T(nil)`
// conversion, a comma-ok map read, a range over a slice, a blank discard.
const exprTypeSrc = `package main

type pair struct{ a, b int }

func (p pair) sum() int { return p.a + p.b }

func zero()            {}
func one() int         { return 1 }
func two() (int, bool) { return 2, true }

func subject(n int) int {
	var err error
	err = nil
	e2 := error(nil)
	_ = n + 1
	zero()
	a, ok := two()
	m := map[string]int{"k": 1}
	v, found := m["k"]
	_, found2 := m["k"]
	_ = m["k"]
	s := []int{1, 2, 3}
	_ = s[0]
	p := pair{a: 1, b: 2}
	_ = p.a
	f := func(x int) int { return x * 2 }
	_ = f(3)
	_ = one()
	_, _ = two()
	arr := [2]int{4, 5}
	ch := make(chan int)
	close(ch)
	for range s {
		n++
	}
	for range "ab" {
		n++
	}
	for range 3 {
		n++
	}
	for range arr {
		n++
	}
	for range &arr {
		n++
	}
	for range ch {
		n++
	}
	if err != nil || e2 != nil || !ok || !found || !found2 {
		return -1
	}
	return n + one() + a + v + s[0] + p.sum() + f(3) + int(int8(n))
}
`

// walkExprNodes calls visit on every wire node carrying an `expr` tag.
func walkExprNodes(v any, path string, visit func(path string, node map[string]any)) {
	switch x := v.(type) {
	case map[string]any:
		if _, isExpr := x["expr"]; isExpr {
			visit(path, x)
		}
		for k, c := range x {
			walkExprNodes(c, path+"."+k, visit)
		}
	case []any:
		for i, c := range x {
			walkExprNodes(c, path+"["+strconv.Itoa(i)+"]", visit)
		}
	}
}

// walkStmtNodes calls visit on every wire node carrying a `stmt` tag.
func walkStmtNodes(v any, path string, visit func(path string, node map[string]any)) {
	switch x := v.(type) {
	case map[string]any:
		if _, isStmt := x["stmt"]; isStmt {
			visit(path, x)
		}
		for k, c := range x {
			walkStmtNodes(c, path+"."+k, visit)
		}
	case []any:
		for i, c := range x {
			walkStmtNodes(c, path+"["+strconv.Itoa(i)+"]", visit)
		}
	}
}

// resultArity returns the length of a call-shaped node's `resultTypes`
// vector and whether the node carries one.
func resultArity(node map[string]any) (int, bool) {
	rts, ok := node["resultTypes"]
	if !ok {
		return 0, false
	}
	switch v := rts.(type) {
	case []any:
		return len(v), true
	case []map[string]any:
		return len(v), true
	}
	return 0, true
}

// Every node at an `exprTypeOf` consumer position carries `type` — the rhs
// of every blank-target assignment that the decoder's blank path reaches
// (not a call-shaped rhs, not the comma-ok `map-get`), and the collection
// of every indexable/channel range — and the fixture exercises each shape
// (the counts guard against a vacuous pass); the two typeless-by-name
// shapes (the bare `nil`, the tuple-typed call) do occur and are typeless.
func TestConsumerPositionsCarryTypeAndCarveOutsAreByName(t *testing.T) {
	program, err := emitSource(t, exprTypeSrc)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	if r := stubReason(t, program, "subject"); r != "" {
		t.Fatalf("subject must lower with a body, got the refusal %q", r)
	}
	blankRhs, rangeColl := 0, 0
	rangeKinds := map[string]bool{}
	walkStmtNodes(program["funcs"], "funcs", func(path string, node map[string]any) {
		switch node["stmt"] {
		case "assign":
			lhs, _ := node["lhs"].([]any)
			rhs, _ := node["rhs"].([]any)
			blank := false
			for _, l := range lhs {
				if lm, ok := l.(map[string]any); ok && lm["target"] == "blank" {
					blank = true
				}
			}
			if !blank {
				return
			}
			for i, r := range rhs {
				rm, ok := r.(map[string]any)
				if !ok {
					continue
				}
				if _, callShaped := resultArity(rm); callShaped {
					continue // routed through resultTypes before the blank path
				}
				if len(lhs) == 2 && len(rhs) == 1 && rm["expr"] == "map-get" {
					continue // the comma-ok read, routed through asMapGet? first
				}
				blankRhs++
				if _, has := rm["type"]; !has {
					t.Errorf("blank-assignment rhs[%d] node %v at %s carries no `type` (the decoder declares the discard temporary from it)", i, rm["expr"], path)
				}
			}
		case "range":
			kind, _ := node["kind"].(string)
			switch kind {
			case "slice", "array", "int", "array-pointer", "chan", "string":
			default:
				return
			}
			coll, ok := node["collection"].(map[string]any)
			if !ok {
				t.Errorf("range at %s has no collection node", path)
				return
			}
			rangeColl++
			rangeKinds[kind] = true
			if _, has := coll["type"]; !has {
				t.Errorf("range (%s) collection node %v at %s carries no `type` (the decoder declares $rcoll from it)", kind, coll["expr"], path)
			}
		}
	})
	if blankRhs < 4 {
		t.Errorf("expected at least 4 non-call blank-assignment rhs positions in the fixture (n+1, m[k], s[0], p.a), saw %d", blankRhs)
	}
	// (a key-less, value-less range over an array or array pointer lowers to
	// another kind; the array kinds are checked when present, not demanded)
	for _, k := range []string{"slice", "string", "int", "chan"} {
		if !rangeKinds[k] {
			t.Errorf("the fixture's range over %s did not reach the wire as a range statement of that kind (saw %v)", k, rangeKinds)
		}
	}
	typelessNil, sawTuple := 0, 0
	walkExprNodes(program["funcs"], "funcs", func(path string, node map[string]any) {
		if node["expr"] == "nil" {
			// the conversion form `error(nil)` carries its target (BUG-077);
			// the assignment form `err = nil` is typeless by name
			if _, has := node["type"]; !has {
				typelessNil++
			}
		}
		if n, callShaped := resultArity(node); callShaped && n != 1 {
			sawTuple++
			if _, has := node["type"]; has {
				t.Errorf("tuple-typed call node at %s carries a `type` (no wire type spells a tuple)", path)
			}
		}
	})
	if typelessNil == 0 {
		t.Errorf("the fixture's bare `nil` assignment did not reach the wire as a typeless nil node")
	}
	if sawTuple == 0 {
		t.Errorf("the fixture's zero- and two-result calls did not reach the wire as call nodes with resultTypes of length != 1")
	}
}

// emitSourceWith is emitSource with a hook on the type-checker's results
// before emission — the one way to make `typeOf` fail on a real wire path
// (go/types types every value expression of a program it accepts).
func emitSourceWith(t *testing.T, src string, mutate func(info *types.Info, f *ast.File)) (map[string]any, error) {
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
	mutate(info, f)
	e := &emitter{fset: fset, info: info, pkg: pkg}
	return e.emitProgram([]*ast.File{f})
}

// A `typeOf` failure on the discard rhs SURFACES as the declaration's
// refusal naming the expression and its position — it is not swallowed by
// omitting the key. The failure is forced by erasing the type-checker's
// record of the `n + 1` node (a *ast.BinaryExpr, so `typeOf` has no ident
// fallback): the emitter must then refuse, not emit a typeless node.
func TestTypeOfFailureSurfacesAsRefusal(t *testing.T) {
	src := `package main
func subject(n int) int {
	_ = n + 1
	return n
}
`
	erased := 0
	program, err := emitSourceWith(t, src, func(info *types.Info, f *ast.File) {
		ast.Inspect(f, func(node ast.Node) bool {
			if b, ok := node.(*ast.BinaryExpr); ok {
				delete(info.Types, b)
				erased++
			}
			return true
		})
	})
	if erased != 1 {
		t.Fatalf("expected to erase exactly one binary expression's type record, erased %d", erased)
	}
	if err != nil {
		t.Fatalf("the per-declaration quarantine keeps the export OK: %v", err)
	}
	reason := stubReason(t, program, "subject")
	if reason == "" {
		t.Fatalf("a typeOf failure must quarantine the declaration by name, not reach the wire as a typeless node:\n%s", mustJSON(t, program))
	}
	for _, want := range []string{"no type for expression", "*ast.BinaryExpr", "main.go:3"} {
		if !strings.Contains(reason, want) {
			t.Errorf("the refusal must carry %q:\n%s", want, reason)
		}
	}
}
