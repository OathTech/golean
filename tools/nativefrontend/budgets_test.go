package main

// Unit tests for the per-declaration materialization budgets (BUG-078 /
// F2, budgets.go). The corpus rows (Corpus/coverage/exec/arrays/
// materialization-budget-quarantine and the three moved over-budget rows)
// pin the observable contract — the unrelated subjects run, each
// over-budget declaration refuses by name. These pin what the differential
// cannot see: the table is the source of the numbers, each quarantine
// UNIT (function stub, var poison, type marker, signature marker), the
// make precedence, and that NO over-budget shape reaches the wire (the
// decoder would refuse the whole wire on it).

import (
	"encoding/json"
	"fmt"
	"strings"
	"testing"
)

func findFunc(program map[string]any, name string) map[string]any {
	fs, _ := program["funcs"].([]any)
	for _, f := range fs {
		if fm, ok := f.(map[string]any); ok && fm["name"] == name {
			return fm
		}
	}
	return nil
}

func findTypeDef(program map[string]any, name string) map[string]any {
	ts, _ := program["types"].([]any)
	for _, t := range ts {
		if tm, ok := t.(map[string]any); ok && tm["name"] == name {
			return tm
		}
	}
	return nil
}

// wireArrayLens: every "array" node's len anywhere in the wire.
func wireArrayLens(t *testing.T, program map[string]any) []int64 {
	t.Helper()
	raw, err := json.Marshal(program)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	var generic any
	if err := json.Unmarshal(raw, &generic); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}
	var out []int64
	var walk func(any)
	walk = func(v any) {
		switch x := v.(type) {
		case map[string]any:
			if x["kind"] == "array" {
				if l, ok := x["len"].(float64); ok {
					out = append(out, int64(l))
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
	walk(generic)
	return out
}

func TestBudgetsTableIsTheSource(t *testing.T) {
	// The embedded table parses and carries the four numbers; the Lean
	// side (Tests/GoCoreEval.lean budgetsTableTests) pins them to the
	// decoder's constants.
	if budgets.arrayLen <= 0 || budgets.arrayFootprint <= 0 || budgets.sliceCap <= 0 || budgets.maxAllocBytes <= 0 {
		t.Fatalf("budgets not loaded: %+v", budgets)
	}
	// Malformed tables refuse (fail closed): a missing row, a duplicate,
	// an unknown name, a non-positive value, a wrong header.
	good := "name\tvalue\tlean\narrayLenBudget\t1\tA\narrayFootprintBudget\t2\tB\nsliceCapBudget\t3\tC\nmaxAllocBytes\t4\tD\n"
	if _, err := parseBudgets(good); err != nil {
		t.Fatalf("good table refused: %v", err)
	}
	for name, bad := range map[string]string{
		"missing":   "name\tvalue\tlean\narrayLenBudget\t1\tA\n",
		"duplicate": good + "arrayLenBudget\t1\tA\n",
		"unknown":   good + "fooBudget\t1\tA\n",
		"zero":      strings.Replace(good, "\t1\t", "\t0\t", 1),
		"header":    strings.Replace(good, "name\tvalue\tlean", "name\tvalue", 1),
	} {
		if _, err := parseBudgets(bad); err == nil {
			t.Errorf("%s table accepted", name)
		}
	}
}

func TestBudgetFunctionQuarantine(t *testing.T) {
	src := fmt.Sprintf(`package main

func big() int { a := [%d]int{1: 5}; return a[1] }

func atBudget() int { var a [%d]byte; return len(a) }

func ok() int { return 7 }
`, budgets.arrayLen+1, budgets.arrayLen)
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused (want a per-declaration quarantine): %v", err)
	}
	stub := findFunc(program, "big")
	if stub == nil || !strings.Contains(fmt.Sprint(stub["unsupported"]), "materialization budget (BUG-078)") ||
		!strings.Contains(fmt.Sprint(stub["unsupported"]), "arrayLenBudget") {
		t.Fatalf("big is not a budget stub: %v", stub)
	}
	if f := findFunc(program, "atBudget"); f == nil || f["unsupported"] != nil {
		t.Fatalf("atBudget (AT the budget, strict >) was refused: %v", f)
	}
	if f := findFunc(program, "ok"); f == nil || f["unsupported"] != nil {
		t.Fatalf("ok was refused: %v", f)
	}
	for _, l := range wireArrayLens(t, program) {
		if l > budgets.arrayLen {
			t.Fatalf("an over-budget array type (len %d) reached the wire", l)
		}
	}
}

func TestBudgetNestedAndTypeMarker(t *testing.T) {
	// [4096][4097]byte: every dimension in budget, the product over.
	src := `package main

type Grid [4096][4097]byte

type Holder struct{ p *Grid }

type Getter interface{ Get() Grid }

func (g *Grid) Get() Grid { return *g }

func useGrid() int { var g Grid; return int(g[0][0]) }

func useHolder() int { var h Holder; _ = h; return 1 }

func ok() int { return 7 }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused (want per-declaration quarantine): %v", err)
	}
	for _, name := range []string{"main.Grid", "main.Holder"} {
		td := findTypeDef(program, name)
		def, _ := td["def"].(map[string]any)
		if def["kind"] != "unsupported" || !strings.Contains(fmt.Sprint(def["feature"]), "materialization budget (BUG-078)") {
			t.Fatalf("%s is not a budget marker: %v", name, td)
		}
	}
	for _, name := range []string{"useGrid", "useHolder"} {
		if f := findFunc(program, name); f == nil || !strings.Contains(fmt.Sprint(f["unsupported"]), "materialization budget") {
			t.Fatalf("%s is not a budget stub: %v", name, f)
		}
	}
	if m := findMethod(program, "main.Grid", "Get"); m == nil || m["unsupported"] == nil {
		t.Fatalf("Grid.Get is not a signature-carrying stub: %v", m)
	}
	if f := findFunc(program, "ok"); f == nil || f["unsupported"] != nil {
		t.Fatalf("ok was refused: %v", f)
	}
	for _, l := range wireArrayLens(t, program) {
		if l > 4096 {
			t.Fatalf("an over-budget array type (len %d) reached the wire", l)
		}
	}
}

func TestBudgetGlobalPoison(t *testing.T) {
	src := fmt.Sprintf(`package main

var big = [%d]int{3: 7}

func read() int { return big[3] }

func ok() int { return 7 }
`, budgets.arrayLen+1)
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused (want the FR-24 poison): %v", err)
	}
	gs, _ := program["globals"].([]any)
	if len(gs) != 1 || !strings.Contains(fmt.Sprint(gs[0]), poisonedCellTypeId) {
		t.Fatalf("big is not poisoned: %v", gs)
	}
	if f := findFunc(program, "read"); f == nil || !strings.Contains(fmt.Sprint(f["unsupported"]), "materialization budget (BUG-078)") {
		t.Fatalf("read is not a budget stub: %v", f)
	}
	if f := findFunc(program, "ok"); f == nil || f["unsupported"] != nil {
		t.Fatalf("ok was refused: %v", f)
	}
}

func TestBudgetSignatureMarker(t *testing.T) {
	// An over-budget inline array in a METHOD SIGNATURE: the method stubs
	// and the signature names an opaque marker (satisfaction answers);
	// the export survives.
	src := fmt.Sprintf(`package main

type T struct{}

type I interface{ M([%d]int) }

func (T) M(a [%[1]d]int) {}

func ok() int { var x any = T{}; _, isI := x.(I); if isI { return 1 }; return 0 }
`, budgets.arrayLen+1)
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused (want a signature marker): %v", err)
	}
	key := fmt.Sprintf("[%d]int", budgets.arrayLen+1)
	td := findTypeDef(program, key)
	def, _ := td["def"].(map[string]any)
	if def["kind"] != "unsupported" {
		t.Fatalf("no opaque marker %s: %v", key, td)
	}
	if m := findMethod(program, "main.T", "M"); m == nil || m["unsupported"] == nil {
		t.Fatalf("T.M is not a stub: %v", m)
	}
	if f := findFunc(program, "ok"); f == nil || f["unsupported"] != nil {
		t.Fatalf("ok was refused: %v", f)
	}
}

func TestBudgetMakePrecedence(t *testing.T) {
	// over: 1<<15 x [1024]byte = 2^25 leaves. at: 1<<14 (2^24, strict >).
	// maxalloc: gc's own makeslice panic first. capcount: past
	// sliceCapBudget, the machine's own refusal. mixed: a run-time cap
	// beside a constant len drives nothing. capover: a constant cap owns
	// the count.
	src := `package main

func over() int     { return len(make([][1024]byte, 1<<15)) }
func at() int       { return len(make([][1024]byte, 1<<14)) }
func maxalloc() int { return len(make([][1024]byte, 1<<40)) }
func capcount() int { return len(make([][1]byte, 1<<24)) }
func mixed(n int) int { return len(make([][1024]byte, 1<<15, n)) }
func capover() int  { return len(make([][1024]byte, 1, 1<<15)) }
func runtime(n int) int { return len(make([][1024]byte, n)) }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused: %v", err)
	}
	for name, wantStub := range map[string]bool{
		"over": true, "at": false, "maxalloc": false, "capcount": false,
		"mixed": false, "capover": true, "runtime": false,
	} {
		f := findFunc(program, name)
		if f == nil {
			t.Fatalf("%s missing", name)
		}
		isStub := strings.Contains(fmt.Sprint(f["unsupported"]), "materialization budget (BUG-078)")
		if isStub != wantStub {
			t.Errorf("%s: budget stub = %v, want %v (%v)", name, isStub, wantStub, f["unsupported"])
		}
	}
}
