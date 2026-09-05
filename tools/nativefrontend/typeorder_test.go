package main

// G-C2 wire-half guards (2026-09-05, design note
// docs/2026-09-05_c-arc-c2-design.md): the emitted `types` table is in
// dependency order (struct-field / array-elem / defined-target edges),
// the ordering is deterministic, and the pure ordering/check functions
// refuse cycles, dangling names and alias defs by name.

import (
	"encoding/json"
	"strings"
	"testing"
)

// Types DECLARED in reverse dependency order, with pointer/slice/map
// self-recursion (legal; not edges) alongside real array/field edges.
const typeOrderSrc = `package main

type Outer struct {
	in  Inner
	arr [2]Mid
	p   *Outer
	s   []Outer
	m   map[string]Inner
}
type Mid struct {
	x  Inner
	ys [3][2]Inner
}
type Inner struct{ n int }
type Ring struct {
	next  *Ring
	items []Ring
}
type Code int
type Codes [4]Code

func main() {
	var o Outer
	var r Ring
	var c Codes
	println(o.in.n, r.next == nil, len(c))
}
`

func typeIndex(t *testing.T, program map[string]any) map[string]int {
	t.Helper()
	idx := map[string]int{}
	for i, td := range program["types"].([]any) {
		idx[td.(map[string]any)["name"].(string)] = i
	}
	return idx
}

func TestTypeTableIsDependencyOrderedAndDeterministic(t *testing.T) {
	const runs = 20
	first := emitOnce(t, typeOrderSrc)
	if strings.HasPrefix(first, "REFUSED: ") {
		t.Fatalf("type-order shape must export: %s", first)
	}
	for i := 1; i < runs; i++ {
		if got := emitOnce(t, typeOrderSrc); got != first {
			t.Fatalf("emission %d differs from emission 0 (type ordering reached a map iteration)\n--- 0:\n%.400s\n--- %d:\n%.400s", i, first, i, got)
		}
	}
	program, err := emitSource(t, typeOrderSrc)
	if err != nil {
		t.Fatal(err)
	}
	if err := checkTypeDefOrder(program["types"].([]any)); err != nil {
		t.Fatalf("emitted table violates the order contract: %v", err)
	}
	idx := typeIndex(t, program)
	for _, n := range []string{"main.Inner", "main.Mid", "main.Outer", "main.Code", "main.Codes", "main.Ring"} {
		if _, ok := idx[n]; !ok {
			t.Fatalf("type %s missing from the table: %v", n, idx)
		}
	}
	if !(idx["main.Inner"] < idx["main.Mid"] && idx["main.Mid"] < idx["main.Outer"]) {
		t.Fatalf("want Inner < Mid < Outer, got %v", idx)
	}
	if !(idx["main.Code"] < idx["main.Codes"]) {
		t.Fatalf("want Code < Codes, got %v", idx)
	}
}

// ---- hand-built tables ----

func named(n string) map[string]any { return map[string]any{"kind": "named", "name": n} }

func structDef(name string, fieldTypes ...any) map[string]any {
	fields := []any{}
	for i, ft := range fieldTypes {
		fields = append(fields, map[string]any{"name": "f" + itoa(i), "type": ft, "embedded": false})
	}
	return map[string]any{"name": name, "def": map[string]any{"kind": "struct", "fields": fields}}
}

func definedDef(name string, target any) map[string]any {
	return map[string]any{"name": name, "def": map[string]any{"kind": "defined", "target": target}}
}

func tableNames(tds []any) []string {
	out := []string{}
	for _, td := range tds {
		out = append(out, td.(map[string]any)["name"].(string))
	}
	return out
}

func TestOrderTypeDefsCycleRefuses(t *testing.T) {
	_, err := orderTypeDefsByDependency([]any{
		structDef("main.A", named("main.B")),
		structDef("main.B", named("main.A")),
	})
	if err == nil {
		t.Fatal("struct field cycle must refuse")
	}
	msg := err.Error()
	for _, want := range []string{"cycle", "main.A", "main.B", "main.A -> main.B -> main.A"} {
		if !strings.Contains(msg, want) {
			t.Fatalf("cycle refusal must contain %q: %s", want, msg)
		}
	}
	// A cycle through an array elem and a defined target is a cycle too.
	_, err = orderTypeDefsByDependency([]any{
		definedDef("main.C", map[string]any{"kind": "array", "len": int64(2), "elem": named("main.D")}),
		structDef("main.D", named("main.C")),
	})
	if err == nil || !strings.Contains(err.Error(), "cycle") {
		t.Fatalf("array/defined cycle must refuse naming a cycle: %v", err)
	}
}

func TestOrderTypeDefsDanglingRefuses(t *testing.T) {
	_, err := orderTypeDefsByDependency([]any{structDef("main.A", named("main.Missing"))})
	if err == nil || !strings.Contains(err.Error(), "main.Missing") || !strings.Contains(err.Error(), "main.A") {
		t.Fatalf("dangling dependency must refuse naming both ends: %v", err)
	}
	if err := checkTypeDefOrder([]any{structDef("main.A", named("main.Missing"))}); err == nil || !strings.Contains(err.Error(), "main.Missing") {
		t.Fatalf("checkTypeDefOrder must refuse a dangling dependency by name: %v", err)
	}
	// The decoder-synthesized struct{} is the one name always satisfied.
	out, err := orderTypeDefsByDependency([]any{structDef("main.A", named(emptyStructName))})
	if err != nil || len(out) != 1 {
		t.Fatalf("struct{} dependency must be satisfied without a TypeDef: %v", err)
	}
	if err := checkTypeDefOrder(out); err != nil {
		t.Fatal(err)
	}
}

func TestOrderTypeDefsAlreadyOrderedUnchanged(t *testing.T) {
	in := []any{
		structDef("main.Inner", map[string]any{"kind": "int", "int": "int"}),
		definedDef("main.Code", map[string]any{"kind": "int", "int": "int"}),
		structDef("main.Mid", named("main.Inner"), map[string]any{"kind": "array", "len": int64(3), "elem": named("main.Inner")}),
		map[string]any{"name": "main.I", "def": map[string]any{"kind": "interface", "methods": []any{}}},
		map[string]any{"name": "pkg.Opaque", "def": map[string]any{"kind": "unsupported", "feature": "x"}},
		structDef("main.Outer", named("main.Inner"), named("main.Mid"), map[string]any{"kind": "pointer", "elem": named("main.Outer")}),
	}
	before := tableNames(in)
	out, err := orderTypeDefsByDependency(in)
	if err != nil {
		t.Fatal(err)
	}
	if got := tableNames(out); strings.Join(got, ",") != strings.Join(before, ",") {
		t.Fatalf("already-valid table must keep its order\nwant %v\n got %v", before, got)
	}
	if err := checkTypeDefOrder(out); err != nil {
		t.Fatal(err)
	}
}

func TestOrderTypeDefsReversedIsReordered(t *testing.T) {
	in := []any{
		structDef("main.Outer", named("main.Inner"), map[string]any{"kind": "array", "len": int64(2), "elem": named("main.Mid")}),
		structDef("main.Mid", named("main.Inner")),
		definedDef("main.Codes", map[string]any{"kind": "array", "len": int64(4), "elem": named("main.Code")}),
		definedDef("main.Code", map[string]any{"kind": "int", "int": "int"}),
		structDef("main.Inner", map[string]any{"kind": "int", "int": "int"}),
	}
	if err := checkTypeDefOrder(in); err == nil {
		t.Fatal("reversed table must FAIL the order check before ordering")
	} else if !strings.Contains(err.Error(), "types[0] main.Outer depends on types[4] main.Inner") {
		t.Fatalf("check must name the first offending edge: %v", err)
	}
	out, err := orderTypeDefsByDependency(in)
	if err != nil {
		t.Fatal(err)
	}
	if len(out) != len(in) {
		t.Fatalf("not a permutation: %d vs %d", len(out), len(in))
	}
	if err := checkTypeDefOrder(out); err != nil {
		t.Fatalf("ordered table fails the check: %v", err)
	}
	// DFS post-order in current table order: Outer's deps first (Inner,
	// then Mid), then Outer, then Codes' dep Code, then Codes.
	want := "main.Inner,main.Mid,main.Outer,main.Code,main.Codes"
	if got := strings.Join(tableNames(out), ","); got != want {
		t.Fatalf("want %s\n got %s", want, got)
	}
}

func TestOrderTypeDefsIndirectRecursionIsNotACycle(t *testing.T) {
	in := []any{
		structDef("main.L",
			map[string]any{"kind": "pointer", "elem": named("main.L")},
			map[string]any{"kind": "slice", "elem": named("main.L")},
			map[string]any{"kind": "map", "key": map[string]any{"kind": "string"}, "value": named("main.L")},
			map[string]any{"kind": "chan", "dir": "both", "elem": named("main.L")},
			map[string]any{"kind": "func", "params": []any{named("main.L")}, "results": []any{named("main.L")}}),
		structDef("main.M", map[string]any{"kind": "pointer", "elem": named("main.N")}),
		structDef("main.N", map[string]any{"kind": "slice", "elem": named("main.M")}),
	}
	out, err := orderTypeDefsByDependency(in)
	if err != nil {
		t.Fatalf("pointer/slice/map/chan/func recursion is not a cycle: %v", err)
	}
	if got := strings.Join(tableNames(out), ","); got != "main.L,main.M,main.N" {
		t.Fatalf("no edges => order unchanged, got %s", got)
	}
	if err := checkTypeDefOrder(out); err != nil {
		t.Fatal(err)
	}
}

func TestOrderTypeDefsAliasRefuses(t *testing.T) {
	in := []any{map[string]any{"name": "main.Al", "def": map[string]any{"kind": "alias", "target": named("main.X")}}}
	if _, err := orderTypeDefsByDependency(in); err == nil || !strings.Contains(err.Error(), "alias") || !strings.Contains(err.Error(), "main.Al") {
		t.Fatalf("alias def must refuse by name: %v", err)
	}
	if err := checkTypeDefOrder(in); err == nil || !strings.Contains(err.Error(), "alias") {
		t.Fatalf("checkTypeDefOrder must refuse an alias def: %v", err)
	}
	// An unknown def kind refuses too (a new kind must choose its edges).
	if _, err := orderTypeDefsByDependency([]any{map[string]any{"name": "main.Z", "def": map[string]any{"kind": "novel"}}}); err == nil || !strings.Contains(err.Error(), "novel") {
		t.Fatalf("unknown def kind must refuse by name: %v", err)
	}
}

// The determinism cases of determinism_test.go also carry types; make
// sure the emitted wire there passes the order check as well.
func TestDeterminismShapesPassTypeOrder(t *testing.T) {
	program, err := emitSource(t, detMultiSrc)
	if err != nil {
		t.Fatal(err)
	}
	if err := checkTypeDefOrder(program["types"].([]any)); err != nil {
		t.Fatalf("multi-quarantine shape table violates the order contract: %v", err)
	}
	if _, err := json.Marshal(program); err != nil {
		t.Fatal(err)
	}
}
