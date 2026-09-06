package main

// identity_test.go — the identity/display boundary (lane fr19-bug097,
// docs/2026-09-05_fr19-bug097-design.md): keys are path-qualified and
// scope-disambiguated, displays are gc's NameString spellings (verified
// against the go1.26.5 probe transcripts in
// docs/evidence/2026-09-05_fr19-bug097/gc-probes.txt).

import (
	"go/token"
	"go/types"
	"strconv"
	"strings"
	"testing"
)

const identityTestSrc = `package main

type T int

func (T) Get() int { return 1 }
func (T) get() int { return 1 }

type S struct{ X int }

func (S) A() {}

func localA() any { type L int; return L(1) }
func localB() any { type L int; return L(2) }

func shadow() any {
	type S struct{ v int }
	return S{1}
}

var (
	vFunc    func(int, ...string) (int, error)
	vSend    chan<- T
	vRecv    <-chan T
	vChanOf  chan (<-chan T)
	vMap     map[string][]T
	vArr     [3]*T
	vStruct  struct {
		S
		X int ` + "`json:\"x\"`" + `
		y T
	}
	vIface   interface{ Z(); A() }
	vUnexp   interface{ get() int; M() }
	vEmbed   interface{ error; Get() int }
	vAny     any
	vErr     error
	vByte    byte
	vRune    rune
	vEmptyS  struct{}
	vNamedR  interface{ Get() T }
)

func main() { _, _, _ = localA(), localB(), shadow() }
`

func varType(t *testing.T, e *emitter, name string) types.Type {
	t.Helper()
	for id, obj := range e.info.Defs {
		if v, ok := obj.(*types.Var); ok && id.Name == name && !v.IsField() {
			return v.Type()
		}
	}
	t.Fatalf("no var %s", name)
	return nil
}

// TestGcTypeStringSpellings: gcTypeString reproduces gc's runtime type
// string (tconv2, fmtTypeIDName) on every shape the probes exercised.
func TestGcTypeStringSpellings(t *testing.T) {
	e, _ := checkSource(t, identityTestSrc)
	want := map[string]string{
		"vFunc":   "func(int, ...string) (int, error)",
		"vSend":   "chan<- main.T",
		"vRecv":   "<-chan main.T",
		"vChanOf": "chan (<-chan main.T)",
		"vMap":    "map[string][]main.T",
		"vArr":    "[3]*main.T",
		"vStruct": `struct { main.S; X int "json:\"x\""; y main.T }`,
		"vIface":  "interface { A(); Z() }",
		"vUnexp":  "interface { M(); main.get() int }",
		"vEmbed":  "interface { Error() string; Get() int }",
		"vAny":    "interface {}",
		"vErr":    "error",
		"vByte":   "uint8",
		"vRune":   "int32",
		"vEmptyS": "struct {}",
		"vNamedR": "interface { Get() main.T }",
	}
	for name, exp := range want {
		got, err := e.gcTypeString(varType(t, e, name))
		if err != nil {
			t.Errorf("%s: %v", name, err)
			continue
		}
		if got != exp {
			t.Errorf("%s: gcTypeString = %q, want %q", name, got, exp)
		}
	}
}

// TestAnonIfaceKeyIsPathQualified: the identity KEY of an anonymous
// interface qualifies unexported method names by package PATH (go/types'
// TypeString never does — probe P3) and orders methods as gc does; its
// display is registered beside it.
func TestAnonIfaceKeyIsPathQualified(t *testing.T) {
	e, _ := checkSource(t, identityTestSrc)
	cases := map[string][2]string{
		"vIface":  {"interface{A();Z()}", "interface { A(); Z() }"},
		"vUnexp":  {"interface{M();main.get() int}", "interface { M(); main.get() int }"},
		"vEmbed":  {"interface{Error() string;Get() int}", "interface { Error() string; Get() int }"},
		"vNamedR": {"interface{Get() main.T}", "interface { Get() main.T }"},
	}
	for name, exp := range cases {
		iface := types.Unalias(varType(t, e, name)).(*types.Interface)
		key, err := e.anonIfaceKey(iface)
		if err != nil {
			t.Fatalf("%s: %v", name, err)
		}
		if key != exp[0] {
			t.Errorf("%s: key %q, want %q", name, key, exp[0])
		}
		if d, ok := e.typeDisplays[key]; !ok || d.display != exp[1] || d.pkg != "" {
			t.Errorf("%s: display record %+v, want {%q, \"\"}", name, d, exp[1])
		}
	}
}

// TestLocalTypeKeysAndDisplays: function-local types key by scope
// ordinal and display as gc does (no scope information); a local type
// shadowing a package-level type keys apart from it; every TypeDef on
// the wire carries display + pkg.
func TestLocalTypeKeysAndDisplays(t *testing.T) {
	program, err := emitSource(t, identityTestSrc)
	if err != nil {
		t.Fatalf("export refused: %v", err)
	}
	seen := map[string]map[string]any{}
	for _, td := range program["types"].([]any) {
		m := td.(map[string]any)
		name := m["name"].(string)
		if _, ok := m["display"].(string); !ok {
			t.Errorf("TypeDef %s has no display field", name)
		}
		if _, ok := m["pkg"].(string); !ok {
			t.Errorf("TypeDef %s has no pkg field", name)
		}
		seen[name] = m
	}
	want := map[string][2]string{
		"main.T":   {"main.T", "main"},
		"main.S":   {"main.S", "main"},
		"main.L·1": {"main.L", "main"},
		"main.L·2": {"main.L", "main"},
		"main.S·3": {"main.S", "main"},
	}
	for key, exp := range want {
		m, ok := seen[key]
		if !ok {
			keys := []string{}
			for k := range seen {
				keys = append(keys, k)
			}
			t.Errorf("TypeDef %s missing; have %s", key, strings.Join(keys, ", "))
			continue
		}
		if m["display"] != exp[0] || m["pkg"] != exp[1] {
			t.Errorf("%s: display/pkg = %v/%v, want %v/%v", key, m["display"], m["pkg"], exp[0], exp[1])
		}
	}
}

// TestUnexportedMethodScopeGuardSinglePackage: the BUG-098 guard is
// silent within one package (requirement and implementation share the
// declaring package).
func TestUnexportedMethodScopeGuardSinglePackage(t *testing.T) {
	e, _ := checkSource(t, identityTestSrc)
	iface := types.Unalias(varType(t, e, "vUnexp")).(*types.Interface)
	e.noteInterface("k", iface)
	if err := e.checkUnexportedMethodScopes(); err != nil {
		t.Fatalf("single-package unexported requirement must not refuse: %v", err)
	}
}

// ---- the emitter's fail-closed refusals at the identity/display boundary
// (audit fix round R5, 2026-09-05: three refusals shipped with no test) ----

// TestAttachTypeDisplaysRefusesUnregisteredKey: a TypeDef whose key has
// no display record was minted outside the boundary constructors — the
// attach pass refuses by name (identity.go attachTypeDisplays).
func TestAttachTypeDisplaysRefusesUnregisteredKey(t *testing.T) {
	e := &emitter{}
	e.noteTypeDisplay("main.Known", typeDisplay{display: "main.Known", pkg: "main"})
	known := map[string]any{"name": "main.Known", "def": map[string]any{"kind": "struct", "fields": []any{}}}
	if err := e.attachTypeDisplays([]any{known}); err != nil {
		t.Fatalf("registered key must attach: %v", err)
	}
	if known["display"] != "main.Known" || known["pkg"] != "main" {
		t.Fatalf("attach wrote %v/%v", known["display"], known["pkg"])
	}
	ghost := map[string]any{"name": "main.Ghost", "def": map[string]any{"kind": "struct", "fields": []any{}}}
	err := e.attachTypeDisplays([]any{known, ghost})
	if err == nil {
		t.Fatal("a TypeDef with no display record must refuse the export")
	}
	if !strings.Contains(err.Error(), "TypeDef main.Ghost has no display record") {
		t.Fatalf("refusal must name the key and the cause; got: %v", err)
	}
}

// TestDisplayConflictRefusal: one key registered with two different
// display records is a minting defect — refused by name, listing the key
// and both records (identity.go noteTypeDisplay / displayConflictRefusal);
// a repeated IDENTICAL registration is not a conflict.
func TestDisplayConflictRefusal(t *testing.T) {
	e := &emitter{}
	e.noteTypeDisplay("main.T", typeDisplay{display: "main.T", pkg: "main"})
	e.noteTypeDisplay("main.T", typeDisplay{display: "main.T", pkg: "main"})
	if err := e.displayConflictRefusal(); err != nil {
		t.Fatalf("an identical re-registration is not a conflict: %v", err)
	}
	e.noteTypeDisplay("main.T", typeDisplay{display: "other.T", pkg: "other"})
	err := e.displayConflictRefusal()
	if err == nil {
		t.Fatal("two different display records for one key must refuse")
	}
	for _, want := range []string{"two different display records", "main.T", "main.T/main", "other.T/other"} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("refusal must contain %q; got: %v", want, err)
		}
	}
	// The attach pass carries the same refusal even when every key is
	// registered (the conflict, not the absence, is the cause).
	td := map[string]any{"name": "main.T", "def": map[string]any{"kind": "struct", "fields": []any{}}}
	if err := e.attachTypeDisplays([]any{td}); err == nil || !strings.Contains(err.Error(), "two different display records") {
		t.Fatalf("attach must refuse on a display conflict; got: %v", err)
	}
}

// TestLocalTypeOrdinalMissingRefuses: a function-local TypeName the
// ordinal table does not know (not among the loaded units' Defs) cannot
// be keyed — recorded and refused by name (identity.go localTypeOrdinal /
// checkLocalTypeOrdinals); the real locals of the same package resolve.
func TestLocalTypeOrdinalMissingRefuses(t *testing.T) {
	e, pkg := checkSource(t, identityTestSrc)
	// Control: a genuine local type has an ordinal and the check is silent.
	var localL *types.TypeName
	for _, obj := range e.info.Defs {
		if tn, ok := obj.(*types.TypeName); ok && tn.Name() == "L" && tn.Parent() != pkg.Scope() {
			localL = tn
			break
		}
	}
	if localL == nil {
		t.Fatal("fixture has no local L")
	}
	if n, ok := e.localTypeOrdinal(localL); !ok || n < 1 {
		t.Fatalf("local L must carry an ordinal, got %d/%v", n, ok)
	}
	if err := e.checkLocalTypeOrdinals(); err != nil {
		t.Fatalf("no phantom yet, check must be silent: %v", err)
	}
	// A phantom local type: declared in a scope below the package scope,
	// unknown to types.Info.Defs.
	phantomScope := types.NewScope(pkg.Scope(), token.NoPos, token.NoPos, "phantom")
	ghost := types.NewTypeName(token.NoPos, pkg, "Ghost", nil)
	types.NewNamed(ghost, types.Typ[types.Int], nil)
	phantomScope.Insert(ghost)
	if _, ok := e.localTypeOrdinal(ghost); ok {
		t.Fatal("a TypeName outside the units' Defs must not receive an ordinal")
	}
	err := e.checkLocalTypeOrdinals()
	if err == nil {
		t.Fatal("a local type without an ordinal must refuse the export")
	}
	if !strings.Contains(err.Error(), "main.Ghost") || !strings.Contains(err.Error(), "without a scope ordinal") {
		t.Fatalf("refusal must name the type and the cause; got: %v", err)
	}
}

// TestKeyPathGrammarRefusesEscapedPaths (audit fix round R11): an import
// path gc's objabi.PathToPrefix would %-escape (non-ASCII, '%', '"') is
// refused at the minting boundary by name, alongside the '.' and '·'
// grammar hazards; a plain ASCII path is not.
func TestKeyPathGrammarRefusesEscapedPaths(t *testing.T) {
	ok := &emitter{}
	ok.pkgQualifier(types.NewPackage("pkgs/naive", "naive"))
	ok.pkgQualifier(types.NewPackage("red/inner", "inner"))
	if err := ok.checkKeyPathGrammar(); err != nil {
		t.Fatalf("ASCII dot-free paths must pass: %v", err)
	}
	cases := map[string]string{
		"pkgs/naïve":       "PathToPrefix",
		"pkgs/100%":        "PathToPrefix",
		"pkgs/\"quoted\"":  "PathToPrefix",
		"example.com/pkgs": "'.'",
		"pkgs/a·b":         "U+00B7",
	}
	for path, want := range cases {
		e := &emitter{}
		e.pkgQualifier(types.NewPackage(path, "p"))
		err := e.checkKeyPathGrammar()
		if err == nil {
			t.Errorf("%q must refuse", path)
			continue
		}
		if !strings.Contains(err.Error(), want) || !strings.Contains(err.Error(), strconv.Quote(path)) {
			t.Errorf("%q: refusal must name the path and the hazard (%s); got: %v", path, want, err)
		}
	}
}
