package main

import (
	"errors"
	"strings"
	"testing"
)

// Stdlib slice 3 (2026-09-04): print/println lowering and the float-bits
// primitive. Red-first: every refusal test below failed against the
// pre-slice frontend with the OLD text `builtin println in statement
// position` (the tests assert the NEW cause-naming texts), and the
// lowering tests failed because no `print`/`float-bits` node existed.

// stmtsOfFunc returns the top-level statements of the named function's body.
func stmtsOfFunc(t *testing.T, program map[string]any, name string) []any {
	t.Helper()
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		ff, ok := f.(map[string]any)
		if !ok || ff["name"] != name {
			continue
		}
		body, _ := ff["body"].(map[string]any)
		stmts, _ := body["body"].([]any)
		return stmts
	}
	t.Fatalf("function %s not in the wire", name)
	return nil
}

func TestPrintLowersAdmittedKinds(t *testing.T) {
	src := `package main
type Code int
func subject() int {
	var u uint8 = 3
	s := "str"
	println(1, s, true, u, Code(7), 'a', -5)
	print("a", 2)
	return 0
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	stmts := stmtsOfFunc(t, program, "subject")
	var prints []map[string]any
	for _, s := range stmts {
		m, _ := s.(map[string]any)
		if m["stmt"] == "print" {
			prints = append(prints, m)
		}
	}
	if len(prints) != 2 {
		t.Fatalf("want 2 print statements, got %d in %v", len(prints), stmts)
	}
	if prints[0]["newline"] != true || len(prints[0]["args"].([]any)) != 7 {
		t.Errorf("println shape: %v", prints[0])
	}
	if prints[1]["newline"] != false || len(prints[1]["args"].([]any)) != 2 {
		t.Errorf("print shape: %v", prints[1])
	}
}

func TestPrintRefusesByName(t *testing.T) {
	cases := []struct {
		name, body, want string
	}{
		{"zero-operands", `println()`, "with zero operands"},
		{"float", `f := 1.5; println(f)`, "floats and complex print through internal/strconv.AppendFloat"},
		{"float-const", `println(1.5)`, "floats and complex print through internal/strconv.AppendFloat"},
		// complex128 refuses EARLIER, at the variable's type (FR-15's
		// unlowerable basic kinds) — the print arm is never reached; the
		// cause is still named.
		{"complex", `c := complex(1, 2); println(c)`, "complex128"},
		{"pointer", `x := 1; println(&x)`, "prints an address in gc"},
		{"nil-pointer", `var p *int; println(p)`, "prints an address in gc"},
		{"slice", `s := []int{1}; println(s)`, "prints an address in gc"},
		{"map", `m := map[int]int{}; println(m)`, "prints an address in gc"},
		{"chan", `ch := make(chan int); println(ch)`, "prints an address in gc"},
		{"func", `f := func() {}; println(f)`, "prints an address in gc"},
		{"interface", `var e any = 1; println(e)`, "prints an address in gc"},
		// A struct operand is gc's REJECTION, not a refusal (BUG-430):
		// the export refuses whole, in the type-check class, with gc's
		// text — TestPrintRejectsArrayAndStructOperandsAsGc has the cells.
		{"struct", `type T struct{}; println(T{})`, "type-check: main.go:3:26: illegal types for operand: print\n\tT"},
	}
	for _, c := range cases {
		src := "package main\nfunc subject() int {\n\t" + c.body + "\n\treturn 0\n}\n"
		refused, msg := exportRefused(t, src)
		// The declaration quarantines per-function (H-3), so the export
		// itself may succeed with a stub; the refusal text must then sit
		// in the stub. Either way the cause must be named.
		if !refused {
			program, err := emitSource(t, src)
			if err != nil {
				t.Fatalf("%s: %v", c.name, err)
			}
			msg = mustJSON(t, program)
		}
		if !strings.Contains(msg, c.want) {
			t.Errorf("%s: refusal does not name its cause %q:\n%s", c.name, c.want, msg)
		}
	}
}

func TestFloatBitsLowersAllFour(t *testing.T) {
	src := `package main
import "math"
func subject(f float64, g float32, u uint64, v uint32) uint64 {
	a := math.Float64bits(f)
	b := math.Float32bits(g)
	c := math.Float64frombits(u)
	d := math.Float32frombits(v)
	_ = b
	_ = c
	_ = d
	return a
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	text := mustJSON(t, program)
	for _, op := range []string{"f64bits", "f32bits", "f64frombits", "f32frombits"} {
		if !strings.Contains(text, `"expr":"float-bits","op":"`+op+`"`) {
			t.Errorf("float-bits op %s not lowered:\n%s", op, text)
		}
	}
	if strings.Contains(text, "frontend-quarantined") || strings.Contains(text, "unsupported") {
		t.Errorf("a float-bits call quarantined:\n%s", text)
	}
}

func TestFloatBitsOtherMathMembersStillRefuse(t *testing.T) {
	// The primitive admits exactly four members; the rest of math keeps
	// its standing refusal (unmodeled package surface), by name.
	src := `package main
import "math"
func subject(f float64) float64 {
	return math.Sqrt(f)
}
`
	refused, msg := exportRefused(t, src)
	if !refused {
		program, err := emitSource(t, src)
		if err != nil {
			t.Fatal(err)
		}
		msg = mustJSON(t, program)
	}
	if !strings.Contains(msg, "math.Sqrt") {
		t.Errorf("math.Sqrt must still refuse by name:\n%s", msg)
	}
	if strings.Contains(msg, "float-bits") {
		t.Errorf("math.Sqrt must not lower through the float-bits primitive:\n%s", msg)
	}
}

func TestStdlibRegisterPrimitivesFull(t *testing.T) {
	dump, err := stdlibRegisterDump()
	if err != nil {
		t.Fatal(err)
	}
	// 3 / cap 3 since window unit 5b (2026-09-30): the `rand-intn` primitive
	// (the cap move RATIFIED [USER] 2026-10-01 at train r58, stdlibregister.go).
	for _, want := range []string{"count\tprimitive\t3 / cap 3", "primitive\tfloat-bits\t", "primitive\tprint-output\t", "primitive\trand-intn\t"} {
		if !strings.Contains(dump, want) {
			t.Errorf("register dump lacks %q", want)
		}
	}
}

// FR-36 (2026-10-06, dotimport.go): the dot-imported spelling reaches the
// SAME object-keyed primitive as the selector spelling. This test's former
// shape (audit fix round D, 2026-09-05) asserted a by-name REFUSAL — the
// stopgap that kept the then-unfixed dot-import class visible; the class fix
// retires it together with the lowerdiag calibration cause
// `dot-import-float-bits`, and the wire must now carry the `float-bits` op.
func TestFloatBitsDotImportLowersToPrimitive(t *testing.T) {
	src := `package main
import . "math"
func subject(f float64) uint64 {
	return Float64bits(f)
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("a dot-imported float-bits call must lower like the qualified spelling (FR-36): %v", err)
	}
	if reason := stubReason(t, program, "subject"); reason != "" {
		t.Fatalf("a dot-imported Float64bits call must not be quarantined: %s", reason)
	}
	msg := mustJSON(t, program)
	if !strings.Contains(msg, `"expr":"float-bits"`) || !strings.Contains(msg, `"op":"f64bits"`) {
		t.Errorf("a dot-imported Float64bits call must lower to the float-bits primitive (op f64bits):\n%s", msg)
	}
	if strings.Contains(msg, `"func":"Float64bits"`) {
		t.Errorf("a dot-imported Float64bits call must not lower as a bare user call (the pre-FR-36 defect):\n%s", msg)
	}
}

// BUG-430 (2026-11-08): an ARRAY or STRUCT operand is gc's rejection —
// walk/builtin.go's operand switch has no arm for TARRAY / TSTRUCT and its
// default calls badtype «illegal types for operand: print» — so the export
// REFUSES WHOLE in the type-check class (a gcRejection, never a
// per-declaration stub that lowers the rest of a program gc does not
// build), naming gc's text and the operand's type. Every cell below was
// measured against gc go1.26.5 under the runners' pins (the lane's
// `.tmp/probes/a*`): gc rejects each of the rejection cells and builds each
// of the admitted ones. The one deliberate divergence is the dead branch:
// gc's writer prunes `if false { … }` before it judges print operands and
// BUILDS that program; the emitter refuses it by name with the clause
// (gcPrintDeadCodeClause, the gclimits.go over-refusal shape).
func TestPrintRejectsArrayAndStructOperandsAsGc(t *testing.T) {
	const gcText = "illegal types for operand: print"
	cases := []struct{ name, decls, body, typeSpelling string }{
		{"array-literal", "", `println([2]int{1, 2})`, "[2]int"},
		{"array-variable", "", `a := [2]int{1, 2}; println(a)`, "[2]int"},
		{"named-array", "type A [2]int", `println(A{1, 2})`, "A"},
		{"zero-array", "", `println([0]int{})`, "[0]int"},
		{"array-of-one-byte", "", `println([1]byte{65})`, "[1]byte"},
		{"empty-struct", "", `println(struct{}{})`, "struct{}"},
		{"named-struct", "type T struct{ x int }", `println(T{1})`, "T"},
		{"named-empty-struct", "type E struct{}", `println(E{})`, "E"},
		{"anon-struct-fields", "", `println(struct{ a int }{1})`, "struct{a int}"},
		{"print-spelling", "", `print([2]int{1, 2})`, "[2]int"},
		{"beside-admitted", "", `println(1, [2]int{1, 2}, "x")`, "[2]int"},
		{"struct-from-call", "func s() struct{ x int } { return struct{ x int }{1} }", `println(s())`, "struct{x int}"},
		{"array-conversion", "type A [2]int", `println([2]int(A{1, 2}))`, "[2]int"},
		{"struct-with-String-method", "type T struct{}\nfunc (T) String() string { return \"T!\" }", `println(T{})`, "T"},
		{"array-deref", "", `a := [2]int{1, 2}; p := &a; println(*p)`, "[2]int"},
		{"in-closure", "", `f := func() { println(struct{}{}) }; f()`, "struct{}"},
		{"in-unused-func", "func unused() { println(struct{}{}) }", `println(2)`, "struct{}"},
		{"in-method", "type T struct{}\nfunc (T) M() { println([2]int{1, 2}) }", `T{}.M()`, "[2]int"},
		{"in-init", "func init() { println([2]int{1, 2}) }", `println(3)`, "[2]int"},
		{"generic-at-struct", "func P[T any](x T) { println(x) }", `P(struct{}{})`, "struct{}"},
		{"generic-method-at-array", "type G[T any] struct{ v T }\nfunc (g G[T]) M() { println(g.v) }", `G[[2]int]{}.M()`, "[2]int"},
		{"spread-struct-component", "func ps() (int, struct{}) { return 1, struct{}{} }", `println(ps())`, "struct{}"},
		{"spread-array-component", "func ta() (int, [2]int) { return 1, [2]int{} }", `println(ta())`, "[2]int"},
		{"dead-branch-over-refusal", "", `if false { println([2]int{}) }; println(1)`, "[2]int"},
	}
	for _, c := range cases {
		src := "package main\n" + c.decls + "\nfunc subject() int {\n\t" + c.body + "\n\treturn 0\n}\n"
		_, err := emitSource(t, src)
		if err == nil {
			t.Errorf("%s: gc rejects this program (%q); the frontend exported it", c.name, gcText)
			continue
		}
		msg := err.Error()
		var rej gcRejection
		if !errors.As(err, &rej) || !strings.HasPrefix(msg, "type-check: main.go:") ||
			!strings.Contains(msg, gcText+"\n\t"+c.typeSpelling+gcPrintDeadCodeClause) {
			t.Errorf("%s: want gc's rejection in the type-check class, at a position, naming %q and the type %q with the dead-code clause; got: %s", c.name, gcText, c.typeSpelling, msg)
		}
		if strings.Contains(msg, "prints an address") {
			t.Errorf("%s: the phantom address cause is back (BUG-430): %s", c.name, msg)
		}
	}
	admitted := []struct{ name, decls, body string }{
		{"struct-field-of-basic-kind", "type T struct{ x int }", `println(T{1}.x)`},
		{"array-element", "", `println([2]int{1, 2}[0])`},
		{"generic-at-basic-kinds", "func P[T any](x T) { println(x) }", `P(1); P("s"); P(true)`},
		{"generic-never-instantiated", "func P[T any](x T) { println(x) }", `println(0)`},
	}
	for _, c := range admitted {
		src := "package main\n" + c.decls + "\nfunc subject() int {\n\t" + c.body + "\n\treturn 0\n}\n"
		program, err := emitSource(t, src)
		if err != nil {
			t.Errorf("%s: gc builds this program; the frontend refused: %v", c.name, err)
			continue
		}
		if reason := stubReason(t, program, "subject"); reason != "" {
			t.Errorf("%s: gc builds this program; the subject is quarantined: %s", c.name, reason)
		}
	}
}

// BUG-430 (2026-11-08): `println(f())` with a multi-value f is LEGAL — gc's
// typecheck spreads the results into temps before walkPrint (typecheckargs →
// RewriteMultiValueCall) and prints each — and the emitter spreads it the
// same way: the call hoists to a define of fresh temps immediately before
// the print, and the print's operands are those temps, one per result, in
// result order. The differential row
// builtins/sweep-s22-print-output/multi-value-operand pins gc's bytes; this
// pins the WIRE SHAPE at every callee spelling measured (the lane's
// `.tmp/probes/b*`): a plain call, `print`, three results, a nested spread
// `id2(two())`, a parenthesised call, a method call, a func value, a
// generic callee.
func TestPrintSpreadsMultiValueCall(t *testing.T) {
	src := `package main
func two() (int, string) { return 1, "two" }
func three() (int, bool, string) { return 7, true, "s" }
func id2(a int, b string) (int, string) { return a + 1, b + "!" }
type T struct{}
func (T) two() (int, string) { return 1, "two" }
func pair[X any](x X) (X, X) { return x, x }
func subject() int {
	println(two())
	print(two())
	println(three())
	println(id2(two()))
	println((two()))
	println(T{}.two())
	f := two
	println(f())
	println(pair(4))
	return 0
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	if reason := stubReason(t, program, "subject"); reason != "" {
		t.Fatalf("a multi-value print operand is legal Go; the subject is quarantined: %s", reason)
	}
	wantArity := []int{2, 2, 3, 2, 2, 2, 2, 2}
	wantNewline := []bool{true, false, true, true, true, true, true, true}
	stmts := stmtsOfFunc(t, program, "subject")
	seen := 0
	for i, s := range stmts {
		m, _ := s.(map[string]any)
		if m["stmt"] != "print" {
			continue
		}
		if seen >= len(wantArity) {
			t.Fatalf("more print statements than expected: %v", stmts)
		}
		args, _ := m["args"].([]any)
		if len(args) != wantArity[seen] || m["newline"] != wantNewline[seen] {
			t.Errorf("print %d: want %d operands, newline=%v; got %v", seen, wantArity[seen], wantNewline[seen], m)
		}
		if i == 0 {
			t.Fatalf("print %d has no preceding statement to hoist the call into: %v", seen, stmts)
		}
		prev, _ := stmts[i-1].(map[string]any)
		lhs, _ := prev["lhs"].([]any)
		rhs, _ := prev["rhs"].([]any)
		if prev["stmt"] != "assign" || prev["define"] != true || len(lhs) != wantArity[seen] || len(rhs) != 1 {
			t.Errorf("print %d: the statement before it must define %d temps from the one call; got %v", seen, wantArity[seen], prev)
		} else {
			for j, a := range args {
				am, _ := a.(map[string]any)
				lm, _ := lhs[j].(map[string]any)
				if am["expr"] != "ident" || lm["target"] != "declare" || am["name"] != lm["id"] {
					t.Errorf("print %d operand %d: want the temp the define declares, got %v vs %v", seen, j, am, lm)
				}
			}
			rm, _ := rhs[0].(map[string]any)
			if rm["expr"] != "call" && rm["expr"] != "method-call" && rm["expr"] != "call-value" {
				t.Errorf("print %d: the define's right-hand side must be the call, got %v", seen, rm)
			}
		}
		seen++
	}
	if seen != len(wantArity) {
		t.Errorf("want %d print statements, saw %d in %v", len(wantArity), seen, stmts)
	}
}

// BUG-430: a spread's COMPONENTS are judged by the same kind rule as a
// plain operand — a pointer or interface result is the address refusal
// (gc prints the address: `1 0x5456b0`, `1 (0x481420,0x497c20)` measured),
// a float result FR-29's — each naming the component as its operand, never
// the tuple as a whole and never the phantom address text for the tuple.
func TestPrintSpreadComponentsJudgedByKind(t *testing.T) {
	cases := []struct{ name, decls, body, want string }{
		{"pointer-component", "var x int\nfunc pp() (int, *int) { return 1, &x }", `println(pp())`, "operand 2 of type *int prints an address in gc"},
		{"interface-component", "func pi() (int, any) { return 1, 2 }", `println(pi())`, "operand 2 of type any prints an address in gc"},
		{"float-component", "func pf() (int, float64) { return 1, 2.5 }", `println(pf())`, "operand 2 of type float64: floats and complex print"},
	}
	for _, c := range cases {
		src := "package main\n" + c.decls + "\nfunc subject() int {\n\t" + c.body + "\n\treturn 0\n}\n"
		program, err := emitSource(t, src)
		if err != nil {
			t.Errorf("%s: a refusal quarantines the declaration, it does not refuse the export: %v", c.name, err)
			continue
		}
		reason := stubReason(t, program, "subject")
		if !strings.Contains(reason, c.want) {
			t.Errorf("%s: want the component judged as operand %q, got stub reason %q", c.name, c.want, reason)
		}
		if strings.Contains(reason, "of type (") {
			t.Errorf("%s: the tuple is named as the operand (the BUG-430 phantom): %q", c.name, reason)
		}
	}
}
