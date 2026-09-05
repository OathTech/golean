package main

import (
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
		{"struct", `type T struct{}; println(T{})`, "prints an address in gc"},
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
	for _, want := range []string{"count\tprimitive\t2 / cap 2", "primitive\tfloat-bits\t", "primitive\tprint-output\t"} {
		if !strings.Contains(dump, want) {
			t.Errorf("register dump lacks %q", want)
		}
	}
}

func TestFloatBitsDotImportRefusesNamingMath(t *testing.T) {
	src := `package main
import . "math"
func subject(f float64) uint64 {
	return Float64bits(f)
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
	if !strings.Contains(msg, "dot-imported math.Float64bits") {
		t.Errorf("a dot-imported float-bits call must refuse naming math:\n%s", msg)
	}
	if strings.Contains(msg, `"expr":"float-bits"`) {
		t.Errorf("a dot-imported float-bits call must not lower:\n%s", msg)
	}
}
