package main

// Unit tests for FR-25 (2026-09-04, lane fr24; the [USER]-approved rider —
// «(3) yes, makes sense», relayed by the coordinator): an unlowerable BASIC
// type (complex64/complex128, unsafe.Pointer) in a method/func SIGNATURE or
// an interface REQUIREMENT list is an opaque `named <basic>` marker with an
// existence-only `unsupported` TypeDef, so the declaration lowers (a stub /
// a requirement), satisfaction answers exactly, and a VALUE of the type or
// a CALL reaching the declaration refuses by name. The differential rows
// (methods/signature-basic-unlowerable/*, init/library-var-type-poisoned/*)
// pin the observable contract; these pin the wire shape.

import (
	"strings"
	"testing"
)

func TestOpaqueBasicInMethodSignatureStubs(t *testing.T) {
	const src = `package main

type U struct{ n int }

func (u U) Bad(c complex128) int { return u.n + int(real(c)) }

func (u U) Good() int { return u.n }

func main() { println(U{n: 1}.Good()) }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("a complex128 method SIGNATURE must be an opaque marker + stub, not a whole-export refusal (FR-25): %v", err)
	}
	td := typeDefByName(program, "complex128")
	if td == nil {
		t.Fatalf("no opaque marker TypeDef for complex128")
	}
	def, _ := td["def"].(map[string]any)
	if def["kind"] != "unsupported" || !strings.Contains(def["feature"].(string), "FR-25") || !strings.Contains(def["feature"].(string), "FR-15") {
		t.Fatalf("marker TypeDef must be the D5 `unsupported` shape naming FR-25 and FR-15: %v", def)
	}
	m := findMethod(program, "main.U", "Bad")
	if m == nil {
		t.Fatalf("stub for U.Bad missing — the method-set entry must never be dropped (satisfaction reads it)")
	}
	reason, _ := m["unsupported"].(string)
	for _, want := range []string{"main.U.Bad", "FR-25: basic type complex128", "FR-15", "opaque marker"} {
		if !strings.Contains(reason, want) {
			t.Fatalf("U.Bad stub reason must contain %q: %q", want, reason)
		}
	}
	params, _ := m["params"].([]any)
	if len(params) != 1 || namedTypeName(params[0].(map[string]any)["type"]) != "complex128" {
		t.Fatalf("the stub must carry the REAL signature with the marker in place: %v", params)
	}
	if g := findMethod(program, "main.U", "Good"); g == nil || g["unsupported"] != nil {
		t.Fatalf("the healthy sibling method must lower: %v", g)
	}
}

func TestOpaqueBasicInInterfaceRequirementList(t *testing.T) {
	// The requirement list stays COMPLETE (audit finding 0: an omitted
	// method is the vacuous-satisfaction hazard): OverflowComplex is present
	// with the marker, so a type WITHOUT it does not satisfy, and the type
	// WITH it (as a stub) does.
	const src = `package main

type Kinder interface {
	Kind() int
	OverflowComplex(x complex128) bool
}

type Yes struct{}

func (Yes) Kind() int                       { return 1 }
func (Yes) OverflowComplex(x complex128) bool { return real(x) > 1 }

type No struct{}

func (No) Kind() int { return 2 }

func kindOf(v any) int {
	if k, ok := v.(Kinder); ok {
		return k.Kind()
	}
	return -1
}

func main() { println(kindOf(Yes{}), kindOf(No{})) }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("an interface whose requirement list mentions complex128 must lower (FR-25): %v", err)
	}
	td := typeDefByName(program, "main.Kinder")
	if td == nil {
		t.Fatalf("interface TypeDef missing")
	}
	def, _ := td["def"].(map[string]any)
	methods, _ := def["methods"].([]any)
	if len(methods) != 2 {
		t.Fatalf("the requirement list must be COMPLETE (2 methods), got %v", methods)
	}
	found := false
	for _, mm := range methods {
		m := mm.(map[string]any)
		if m["name"] == "OverflowComplex" {
			found = true
			params := m["params"].([]any)
			if namedTypeName(params[0]) != "complex128" {
				t.Fatalf("OverflowComplex's parameter must be the complex128 marker: %v", params)
			}
		}
	}
	if !found {
		t.Fatalf("OverflowComplex dropped from the requirement list")
	}
	if typeDefByName(program, "complex128") == nil {
		t.Fatalf("no complex128 marker TypeDef")
	}
	if f := funcByName(program, "kindOf"); f == nil || f["unsupported"] != nil {
		t.Fatalf("kindOf (an assertion against the interface) must lower: %v", f)
	}
}

func TestOpaqueBasicValueInBodyStillRefuses(t *testing.T) {
	// The marker exists in SIGNATURES only: a body that constructs or
	// consumes a complex value refuses on FR-15's own text and quarantines
	// per declaration; the export lives.
	const src = `package main

func mk() complex128 { return complex(1, 2) }

func useIt() float64 { c := mk(); return real(c) }

func fine() int { return 7 }

func main() { println(fine()) }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export must survive (per-declaration quarantine): %v", err)
	}
	for _, fn := range []string{"mk", "useIt"} {
		f := funcByName(program, fn)
		if f == nil {
			t.Fatalf("%s missing", fn)
		}
		r, _ := f["unsupported"].(string)
		if !strings.Contains(r, "complex") {
			t.Fatalf("%s must be a stub naming the complex refusal, got %q", fn, r)
		}
	}
	if f := funcByName(program, "fine"); f == nil || f["unsupported"] != nil {
		t.Fatalf("fine must lower: %v", f)
	}
}

func TestOpaqueBasicStructFieldStillRefusesExport(t *testing.T) {
	// FR-26's shape with FR-15's cause: a struct FIELD of complex type is a
	// TypeDef, not a signature — no marker; the type-declaration pass
	// refuses whole (rowed FR-26). Pinned so a change is deliberate.
	const src = `package main

type P struct {
	z complex128
	n int
}

func fine() int { return 7 }

func main() { println(fine()) }
`
	_, err := emitSource(t, src)
	if err == nil {
		t.Fatalf("a struct TypeDef with a complex field is a whole-export refusal today (FR-26 rowed); a per-declaration answer is a design change that must be recorded")
	}
	if !strings.Contains(err.Error(), "complex128") {
		t.Fatalf("the refusal must name the field type: %v", err)
	}
}

func TestOpaqueBasicPackageVarIsPoisoned(t *testing.T) {
	// Consistency with FR-24: a package-level var OF complex type is not a
	// signature either — its cell poisons per declaration (FR-24), the
	// reader refuses by name, the export lives.
	const src = `package main

var z complex128

func keep(p any) bool { return p != nil }

// (address-of THROUGH a call — the shape that reaches globalAddr and names
// the var; real(z) would refuse on the builtin first, fr24_test.go.)
func readZ() bool { return keep(&z) }

func fine() int { return 7 }

func main() { println(fine()) }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("a package var of complex type must poison per declaration (FR-24): %v", err)
	}
	if g := globalByName(program, "z"); g == nil || namedTypeName(g["type"]) != poisonedCellTypeId {
		t.Fatalf("z must be a %s cell: %v", poisonedCellTypeId, g)
	}
	f := funcByName(program, "readZ")
	if f == nil {
		t.Fatalf("readZ missing")
	}
	if r, _ := f["unsupported"].(string); !strings.Contains(r, "FR-24 poison") || !strings.Contains(r, "complex128") {
		t.Fatalf("readZ must be a stub naming the poisoned var and its type: %q", r)
	}
}
