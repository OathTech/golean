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

// paramTypeName: the `named` marker a wire signature entry's first
// param carries ("" if not a named reference).
func paramTypeName(entry map[string]any) string {
	ps, _ := entry["params"].([]any)
	if len(ps) == 0 {
		return ""
	}
	p, _ := ps[0].(map[string]any)
	ty, _ := p["type"].(map[string]any)
	if ty["kind"] != "named" {
		return ""
	}
	name, _ := ty["name"].(string)
	return name
}

func TestBudgetSignatureMarkerIsCanonical(t *testing.T) {
	// Review BLOCKER-1 (fix round 2026-10-13): Go identity has
	// [N]byte ≡ [N]uint8, [N]rune ≡ [N]int32, an alias ≡ its target, and
	// func types ignore parameter names. The requirement list and the
	// implementing stub must name the SAME marker — one per identity.
	n := budgets.arrayLen + 1
	src := fmt.Sprintf(`package main

type MyByte = byte

type IByte interface{ M([%[1]d]byte) }
type IRune interface{ R([%[1]d]rune) }
type IAlias interface{ A([%[1]d]MyByte) }
type IFunc interface{ F([%[1]d]func(x int) int) }

type T struct{}

func (T) M([%[1]d]uint8)             {}
func (T) R([%[1]d]int32)             {}
func (T) A([%[1]d]uint8)             {}
func (T) F([%[1]d]func(y int) int)   {}
`, n)
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused: %v", err)
	}
	ms, _ := program["methods"].([]any)
	byName := map[string][]string{}
	for _, m := range ms {
		mm := m.(map[string]any)
		id := mm["id"].(memberID).Name
		byName[id] = append(byName[id], paramTypeName(mm))
	}
	for _, name := range []string{"M", "R", "A", "F"} {
		keys := byName[name]
		if len(keys) != 2 || keys[0] == "" || keys[0] != keys[1] {
			t.Errorf("%s: requirement and stub name different markers: %q", name, keys)
		}
	}
	if byName["M"][0] != byName["A"][0] {
		t.Errorf("[N]byte and [N]MyByte (alias) mint different markers: %q vs %q", byName["M"][0], byName["A"][0])
	}
	markers := 0
	ts, _ := program["types"].([]any)
	for _, td := range ts {
		if name, _ := td.(map[string]any)["name"].(string); strings.HasPrefix(name, "[") {
			markers++
		}
	}
	if markers != 3 { // [N]uint8, [N]int32, [N]func(int) int
		t.Errorf("want 3 canonical budget markers, got %d", markers)
	}
}

func TestBudgetStubReasonNamesSignatureMarker(t *testing.T) {
	// Review NIT-1: a method quarantined for ANOTHER reason whose
	// signature carries an over-budget array names the marker.
	src := fmt.Sprintf(`package main

type T struct{}

func (T) M(a [%d]int) complex128 { return 0 }
`, budgets.arrayLen+1)
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused: %v", err)
	}
	m := findMethod(program, "main.T", "M")
	if m == nil || !strings.Contains(fmt.Sprint(m["unsupported"]), "carried as an opaque marker in the signature only") ||
		!strings.Contains(fmt.Sprint(m["unsupported"]), "materialization budget (BUG-078)") {
		t.Fatalf("stub reason does not name the budget marker: %v", m)
	}
}

func TestBudgetInitializerIdioms(t *testing.T) {
	// Review MEDIUM-1: the compile-time interface check and an
	// address-of literal over a budget type are H-11 effect-isolated —
	// skipped and poisoned per declaration, the export survives.
	src := `package main

type Big [70000]int

type Sizer interface{ Size() int }

func (b *Big) Size() int { return len(b) }

var _ Sizer = (*Big)(nil)

var p = &Big{}

func readP() int { return p.Size() }

func ok() int { return 7 }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused (want per-declaration poison): %v", err)
	}
	if f := findFunc(program, "ok"); f == nil || f["unsupported"] != nil {
		t.Fatalf("ok was refused: %v", f)
	}
	if f := findFunc(program, "readP"); f == nil || f["unsupported"] == nil {
		t.Fatalf("readP is not a stub: %v", f)
	}
	// Still whole-export: a call in the initializer, and init code.
	for name, bad := range map[string]string{
		"call": "package main\n\ntype Big [70000]int\n\nfunc makeBig() *Big { return &Big{} }\n\nvar big = makeBig()\n\nfunc ok() int { return 7 }\n",
		"init": "package main\n\nvar n int\n\nfunc init() { var a [70000]int; n = len(a) }\n\nfunc ok() int { return n }\n",
	} {
		_, err := emitSource(t, bad)
		if err == nil || !strings.Contains(err.Error(), "materialization budget (BUG-078)") {
			t.Errorf("%s: want a whole-export budget refusal, got %v", name, err)
		}
		if name == "init" && (err == nil || !strings.Contains(err.Error(), "init function")) {
			t.Errorf("init: the whole-export text does not name init code: %v", err)
		}
	}
}
