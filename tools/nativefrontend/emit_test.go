package main

// Unit tests for the method-set record CLASSIFIER (emit.go,
// methodSetCoverageForKind — class closure of BUG-053, contract note
// docs/2026-08-10_method-set-record-contract.md §3). The S6 audit
// found the original inline switch failed OPEN (`default: full` — an
// unknown/absent def.kind inherited the strongest coverage, the
// retired blanket-true arm relocated to the emitter); these pins make
// a re-introduction of that shape visible forever: every known kind's
// classification is pinned, and the unknown/empty/nameless shapes
// must REFUSE the export, never mint a record.

import (
	"strings"
	"testing"
)

func TestMethodSetCoverageKnownKinds(t *testing.T) {
	cases := []struct {
		kind     string
		coverage string
		carrier  bool
	}{
		{"struct", "full", true},
		{"defined", "full", true},
		{"unsupported", "exported", true},
		{"interface", "", false},
		{"alias", "", false},
	}
	for _, c := range cases {
		coverage, carrier, err := methodSetCoverageForKind("main.T", c.kind)
		if err != nil {
			t.Fatalf("kind %q: unexpected refusal: %v", c.kind, err)
		}
		if carrier != c.carrier || coverage != c.coverage {
			t.Fatalf("kind %q: got (%q, %v), want (%q, %v)",
				c.kind, coverage, carrier, c.coverage, c.carrier)
		}
	}
}

func TestMethodSetCoverageUnknownKindRefuses(t *testing.T) {
	// The BUG-053-class negative: an unknown kind must fail the export
	// (no record, no error-free return) — never classify as `full`.
	for _, kind := range []string{"widget", "generic", "Struct"} {
		coverage, carrier, err := methodSetCoverageForKind("main.T", kind)
		if err == nil {
			t.Fatalf("kind %q: classified (%q, %v) instead of refusing",
				kind, coverage, carrier)
		}
	}
}

func TestMethodSetCoverageEmptyKindRefuses(t *testing.T) {
	// kind "" is what an absent or malformed `def` map yields through
	// the comma-ok extraction — the exact shape the audit flagged.
	if _, _, err := methodSetCoverageForKind("main.T", ""); err == nil {
		t.Fatal("empty kind (absent/malformed def) did not refuse")
	}
}

func TestMethodSetCoverageEmptyNameRefuses(t *testing.T) {
	// A nameless TypeDef must not mint a record keyed "".
	if _, _, err := methodSetCoverageForKind("", "struct"); err == nil {
		t.Fatal("empty TypeDef name did not refuse")
	}
}

// BUG-226: a two-variable range over a pointer to a ZERO-LENGTH array keeps
// its value variable — the value form (`array-pointer`, len 0) exactly where
// gc indexes per iteration (element width 1/2/4/8 on amd64, measured: zero
// iterations, no dereference), a refusal by name at the other widths (gc
// slices the array through the pointer before the loop and a nil pointer
// panics there — measured on string, struct{}, [3]int8, [2]int, any, []int).
func TestRangeZeroLengthArrayPointer(t *testing.T) {
	withStdlibRoots(t)
	findRange := func(t *testing.T, node any) map[string]any {
		t.Helper()
		var found map[string]any
		var walk func(any)
		walk = func(n any) {
			switch v := n.(type) {
			case map[string]any:
				if v["stmt"] == "range" && found == nil {
					found = v
					return
				}
				for _, x := range v {
					walk(x)
				}
			case []any:
				for _, x := range v {
					walk(x)
				}
			}
		}
		walk(node)
		if found == nil {
			t.Fatalf("no range node on the wire")
		}
		return found
	}
	valueForm := []struct{ name, elem string }{
		{"int", "int"}, {"int16", "int16"}, {"int32", "int32"}, {"bool", "bool"}, {"float64", "float64"},
		{"pointer", "*int"}, {"[1]int8", "[1]int8"}, {"8-byte struct", "S8"}, {"uint64", "uint64"},
	}
	for _, c := range valueForm {
		t.Run("value form/"+c.name, func(t *testing.T) {
			dir := writeMain(t, "package main\n\ntype S8 struct{ a, b int32 }\n\nfunc probe() int { var p *[0]"+c.elem+"; n := 0; for i, v := range p { _ = v; n += i }; return n }\n\nfunc main() { println(probe()) }\n")
			prog, err := lowerProgramDir(t, dir)
			if err != nil {
				t.Fatalf("lower: %v", err)
			}
			rng := findRange(t, funcNames(prog)["probe"])
			if rng["kind"] != "array-pointer" || rng["valVar"] == nil || rng["keyVar"] == nil {
				t.Fatalf("want the value form with both variables, got kind=%v keyVar=%v valVar=%v", rng["kind"], rng["keyVar"], rng["valVar"])
			}
			if n, _ := rng["len"].(int64); n != 0 {
				t.Fatalf("want len 0, got %v", rng["len"])
			}
		})
	}
	t.Run("assign form keeps the value temp", func(t *testing.T) {
		dir := writeMain(t, "package main\n\nfunc probe() int { var p *[0]int; n, i, v := 0, 0, 0; for i, v = range p { n += i + v }; return n + i + v }\n\nfunc main() { println(probe()) }\n")
		prog, err := lowerProgramDir(t, dir)
		if err != nil {
			t.Fatalf("lower: %v", err)
		}
		rng := findRange(t, funcNames(prog)["probe"])
		if rng["kind"] != "array-pointer" || rng["valVar"] != "$rangeVal" {
			t.Fatalf("want the value form binding $rangeVal, got kind=%v valVar=%v", rng["kind"], rng["valVar"])
		}
	})
	keyOnly := map[string]string{
		"key only":          "for i := range p { n += i }",
		"key, blank value":  "for i, _ := range p { n += i }",
		"no variables":      "for range p { n++ }",
	}
	for name, loop := range keyOnly {
		t.Run("index form/"+name, func(t *testing.T) {
			dir := writeMain(t, "package main\n\nfunc probe() int { var p *[0]string; n := 0; "+loop+"; return n }\n\nfunc main() { println(probe()) }\n")
			prog, err := lowerProgramDir(t, dir)
			if err != nil {
				t.Fatalf("lower: %v", err)
			}
			rng := findRange(t, funcNames(prog)["probe"])
			if rng["kind"] != "int" || rng["valVar"] != nil {
				t.Fatalf("want the static-length int desugar with no value variable, got kind=%v valVar=%v", rng["kind"], rng["valVar"])
			}
		})
	}
	refused := []struct{ name, elem string }{
		{"string", "string"}, {"struct{}", "struct{}"}, {"[3]int8", "[3]int8"}, {"[2]int", "[2]int"}, {"any", "any"}, {"[]int", "[]int"}, {"16-byte struct", "S16"},
	}
	for _, c := range refused {
		t.Run("refused/"+c.name, func(t *testing.T) {
			dir := writeMain(t, "package main\n\ntype S16 struct{ a, b int }\n\nfunc probe() int { var p *[0]"+c.elem+"; n := 0; for i, v := range p { _ = v; n += i }; return n }\n\nfunc main() { println(probe()) }\n")
			prog, err := lowerProgramDir(t, dir)
			if err != nil {
				t.Fatalf("lower: %v", err)
			}
			// The per-declaration quarantine turns the refusal into a stub
			// carrying its reason in `unsupported`.
			fn := funcNames(prog)["probe"]
			reason, _ := fn["unsupported"].(string)
			if !strings.Contains(reason, "BUG-226") || !strings.Contains(reason, "cheapComputableIndex") {
				t.Fatalf("want probe quarantined with the BUG-226 refusal by name, got %v", fn)
			}
		})
	}
}
