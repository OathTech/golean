package main

// Binding-site shapes after the fix lane frontend/fix-binding-1027
// (2026-10-27): BUG-300 (a grouped `var ( … )` declaration lowers spec by
// spec, the self-shadow capture set is per spec), BUG-301 (a function-local
// interface's dispatch entry is minted once — the called-method anchor pass
// deduplicates against the local declarations too) and BUG-302 (a func
// literal inside a generic function registers its parameters and results
// from the ORIGINAL signature's objects, so the body's uses meet one
// declaration). The differential rows under
// Corpus/coverage/exec/scoping/sweep-s13-grouped-var-spec,
// scoping/sweep-s13-local-iface-dispatch and
// generics/sweep-s13-lit-param-typeparam pin the observations; these pin
// the WIRE SHAPES the observations rest on, so a regression names its
// statement.

import (
	"strings"
	"testing"
)

const bindingSrc = `package main

type Number interface{ ~int | ~int64 }

type Outer struct{ v int }

func (o Outer) Get() int { return o.v }

// BUG-300: the later spec reads the FIRST spec's new x (y = 2).
func groupedVar() int {
	x := 10
	r := 0
	{
		var (
			x = 1
			y = x + 1
		)
		r = x*10 + y
	}
	return r*100 + x
}

// A single spec keeps the one-node shape.
func singleVar() int {
	var x = 1
	return x
}

// BUG-142's rule per spec: the second spec's own name in its initializer
// reads the OUTER x (hoisted), the first spec's y is the new one.
func selfShadowSecondSpec() int {
	x := 10
	r := 0
	{
		var (
			y = 1
			x = x + y
		)
		r = x*10 + y
	}
	return r*100 + x
}

// BUG-142's rule within one spec: both names come into scope at the
// spec's end, so y's initializer reads the OUTER x (hoisted).
func twoNamesOneSpec() int {
	x := 10
	r := 0
	{
		var x, y = 1, x
		r = x*10 + y
	}
	return r*100 + x
}

// BUG-301: a local interface dispatched.
func localIfaceDispatch() int {
	type getter interface{ Get() int }
	var g getter = Outer{1}
	return g.Get()
}

// BUG-302: a literal with a T parameter and a T named result.
func litParamT[T Number](v T) T {
	add := func(d T) (r T) { r = d + v; return }
	return add(1)
}

func useLitParamT() int { return litParamT(1) }

func one() int { return 1 }

// The S28 sweep's grouped forms (scoping/sweep-s28-grouped-decls, regression
// fix lane frontend/fix-grouped-regress-1105): the EMPTY group, the
// parenthesised single spec, a group of one with a call initializer, a
// two-spec group on one line, and an empty const / type group beside them.
func emptyGroup() int {
	var ()
	const ()
	type ()
	var (a = 1)
	var (f = one())
	var (g = 4; h = g + 1)
	return a + f + h
}

func main() {}
`

func bindingProgram(t *testing.T) map[string]any {
	t.Helper()
	program, err := emitSource(t, bindingSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	return program
}

// bodyStmts returns the statements of a function body (or of a wire block).
func bodyStmts(t *testing.T, node map[string]any) []any {
	t.Helper()
	body, ok := node["body"].(map[string]any)
	if ok {
		node = body
	}
	stmts, ok := node["body"].([]any)
	if !ok {
		t.Fatalf("no statement list in %v", node)
	}
	return stmts
}

// innerBlock returns the first wire `block` statement of the function body.
func innerBlock(t *testing.T, fn map[string]any) map[string]any {
	t.Helper()
	for _, s := range bodyStmts(t, fn) {
		if m, ok := s.(map[string]any); ok && m["stmt"] == "block" {
			return m
		}
	}
	t.Fatalf("no inner block in %s", fn["name"])
	return nil
}

func stmtKind(s any) string {
	m, _ := s.(map[string]any)
	k, _ := m["stmt"].(string)
	return k
}

func varDecls(t *testing.T, s any) []map[string]any {
	t.Helper()
	m, _ := s.(map[string]any)
	ds, _ := m["decls"].([]any)
	out := []map[string]any{}
	for _, d := range ds {
		out = append(out, d.(map[string]any))
	}
	return out
}

func TestGroupedVarLowersSpecBySpec(t *testing.T) {
	program := bindingProgram(t)
	stmts := bodyStmts(t, innerBlock(t, wireFunc(t, program, "groupedVar")))
	// Two `var` nodes, one per spec, nothing hoisted before them.
	if len(stmts) < 3 || stmtKind(stmts[0]) != "var" || stmtKind(stmts[1]) != "var" {
		kinds := []string{}
		for _, s := range stmts {
			kinds = append(kinds, stmtKind(s))
		}
		t.Fatalf("groupedVar: expected the block to open with two var nodes, got %v", kinds)
	}
	first, second := varDecls(t, stmts[0]), varDecls(t, stmts[1])
	if len(first) != 1 || first[0]["id"] != "x" || len(second) != 1 || second[0]["id"] != "y" {
		t.Fatalf("groupedVar: expected var x then var y, got %v and %v", first, second)
	}
	// y's initializer is the binary expression inline, and its x names the
	// FIRST spec's declaration (the new x), not a hoisted temp.
	init, _ := second[0]["init"].(map[string]any)
	if init["expr"] != "binary" {
		t.Fatalf("groupedVar: y's initializer must stay inline (binary), got %v", init)
	}
	xRef, _ := init["x"].(map[string]any)
	if xRef["expr"] != "ident" || xRef["name"] != "x" || xRef["local"] != first[0]["local"] {
		t.Errorf("groupedVar: y's x must reference the first spec's declaration (local %v), got %v", first[0]["local"], xRef)
	}
}

func TestSingleSpecVarKeepsOneNode(t *testing.T) {
	program := bindingProgram(t)
	stmts := bodyStmts(t, wireFunc(t, program, "singleVar"))
	if stmtKind(stmts[0]) != "var" || len(varDecls(t, stmts[0])) != 1 {
		t.Errorf("singleVar: expected one var node with one decl, got %v", stmts[0])
	}
}

func TestSelfShadowCaptureIsPerSpec(t *testing.T) {
	program := bindingProgram(t)
	stmts := bodyStmts(t, innerBlock(t, wireFunc(t, program, "selfShadowSecondSpec")))
	// var y; then the hoisted temp for `x + y` (reading the OUTER x and the
	// new y); then var x = $temp.
	kinds := []string{}
	for _, s := range stmts {
		kinds = append(kinds, stmtKind(s))
	}
	if len(stmts) < 4 || kinds[0] != "var" || kinds[1] != "assign" || kinds[2] != "var" {
		t.Fatalf("selfShadowSecondSpec: expected var, assign (hoist), var; got %v", kinds)
	}
	hoist, _ := stmts[1].(map[string]any)
	lhs, _ := hoist["lhs"].([]any)
	target, _ := lhs[0].(map[string]any)
	tmp, _ := target["id"].(string)
	if hoist["define"] != true || !strings.HasPrefix(tmp, "$c") {
		t.Fatalf("selfShadowSecondSpec: the hoist must define a $c temp, got %v", hoist)
	}
	xDecl := varDecls(t, stmts[2])[0]
	init, _ := xDecl["init"].(map[string]any)
	if xDecl["id"] != "x" || init["name"] != tmp {
		t.Errorf("selfShadowSecondSpec: var x must initialize from the temp %s, got %v", tmp, xDecl)
	}
	// The outer x the temp reads is the function's x (declared before the
	// block), never the inner one.
	rhs, _ := hoist["rhs"].([]any)
	bin, _ := rhs[0].(map[string]any)
	xRef, _ := bin["x"].(map[string]any)
	if xRef["local"] == xDecl["local"] {
		t.Errorf("selfShadowSecondSpec: the hoisted read must name the OUTER x, got the inner declaration %v", xRef)
	}
}

func TestTwoNamesOneSpecStillHoists(t *testing.T) {
	program := bindingProgram(t)
	stmts := bodyStmts(t, innerBlock(t, wireFunc(t, program, "twoNamesOneSpec")))
	if stmtKind(stmts[0]) != "assign" || stmtKind(stmts[1]) != "var" {
		t.Fatalf("twoNamesOneSpec: expected the hoist then one var node, got %v", stmts[:2])
	}
	decls := varDecls(t, stmts[1])
	if len(decls) != 2 || decls[0]["id"] != "x" || decls[1]["id"] != "y" {
		t.Fatalf("twoNamesOneSpec: expected one var node declaring x and y, got %v", decls)
	}
	init, _ := decls[1]["init"].(map[string]any)
	if name, _ := init["name"].(string); !strings.HasPrefix(name, "$c") {
		t.Errorf("twoNamesOneSpec: y's initializer must be the hoisted temp (BUG-142), got %v", init)
	}
}

func TestLocalInterfaceDispatchEntryMintedOnce(t *testing.T) {
	program := bindingProgram(t)
	ms, _ := program["methods"].([]any)
	n := 0
	for _, m := range ms {
		mm, _ := m.(map[string]any)
		recv, _ := mm["recvType"].(string)
		if mm["interface"] == true && strings.HasPrefix(recv, "main.getter") && mm["id"].(memberID).Name == "Get" {
			n++
		}
	}
	if n != 1 {
		t.Errorf("localIfaceDispatch: expected exactly one dispatch entry for the local getter.Get, got %d", n)
	}
}

func TestGenericLiteralParamDeclaredOnce(t *testing.T) {
	program := bindingProgram(t)
	fns, _ := program["funcs"].([]any)
	var lit map[string]any
	for _, f := range fns {
		ff, _ := f.(map[string]any)
		if name, _ := ff["name"].(string); strings.HasPrefix(name, "litParamT[int]$lit") {
			lit = ff
		}
	}
	if lit == nil {
		t.Fatalf("the lifted literal of litParamT[int] is not on the wire")
	}
	if u, ok := lit["unsupported"].(string); ok {
		t.Fatalf("the lifted literal refused: %s", u)
	}
	locals, _ := lit["locals"].([]any)
	count := map[string]int{}
	for _, l := range locals {
		e, _ := l.(map[string]any)
		count[e["name"].(string)+"/"+e["kind"].(string)]++
		if e["name"] == "d" && e["kind"] != "param" || e["name"] == "r" && e["kind"] != "result" {
			t.Errorf("unexpected declaration kind in the literal's table: %v", e)
		}
	}
	if count["d/param"] != 1 || count["r/result"] != 1 || count["d/local"] != 0 || count["r/local"] != 0 {
		t.Errorf("the literal's parameter d and result r must each be declared once (param/result), table %v", locals)
	}
}

func TestEmptyAndSingleParenthesisedGroups(t *testing.T) {
	program := bindingProgram(t)
	stmts := bodyStmts(t, wireFunc(t, program, "emptyGroup"))
	kinds := []string{}
	for _, s := range stmts {
		kinds = append(kinds, stmtKind(s))
	}
	// var () is an empty var node; const () and type () are no-op blocks;
	// var (a = 1) one node; var (f = one()) the hoisted call then one node;
	// var (g = 4; h = g + 1) two nodes, h's initializer inline.
	want := []string{"var", "block", "block", "var", "assign", "var", "var", "var", "return"}
	if len(kinds) != len(want) {
		t.Fatalf("emptyGroup: expected %v, got %v", want, kinds)
	}
	for i := range want {
		if kinds[i] != want[i] {
			t.Fatalf("emptyGroup: statement %d expected %s, got %s (all: %v)", i, want[i], kinds[i], kinds)
		}
	}
	if d := varDecls(t, stmts[0]); len(d) != 0 {
		t.Errorf("emptyGroup: var () must declare nothing, got %v", d)
	}
	if d := varDecls(t, stmts[3]); len(d) != 1 || d[0]["id"] != "a" {
		t.Errorf("emptyGroup: var (a = 1) must be one node declaring a, got %v", d)
	}
	hoist, _ := stmts[4].(map[string]any)
	if d := varDecls(t, stmts[5]); hoist["define"] != true || len(d) != 1 || d[0]["id"] != "f" {
		t.Errorf("emptyGroup: var (f = one()) must hoist the call then declare f, got %v / %v", hoist, d)
	}
	g, h := varDecls(t, stmts[6]), varDecls(t, stmts[7])
	if len(g) != 1 || g[0]["id"] != "g" || len(h) != 1 || h[0]["id"] != "h" {
		t.Fatalf("emptyGroup: var (g = 4; h = g + 1) must be two nodes, got %v / %v", g, h)
	}
	init, _ := h[0]["init"].(map[string]any)
	gRef, _ := init["x"].(map[string]any)
	if init["expr"] != "binary" || gRef["local"] != g[0]["local"] {
		t.Errorf("emptyGroup: h's initializer must read g's declaration inline, got %v", init)
	}
}
