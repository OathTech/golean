package main

// Unit tests for the monomorphization identity layer (mono.go), pinning
// the §3.1/§3.2 renderings of docs/2026-08-05_generics-design.md against
// the probe outputs (reflect.Type renderings, go1.26.5) and the registry's
// collision/cap behavior (decisions §9.2/§9.4).

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"strconv"
	"testing"
)

// TestMain runs the whole package's tests under the SAME type-check
// configuration as the frontend binary (audit response m6): run() is
// never called by `go test`, so without this the alias arms
// (types.Unalias paths, materialized *types.Alias) were unreachable in
// tests and a future alias unit would have pinned gotypesalias=0.
func TestMain(m *testing.M) {
	enableMaterializedAliases()
	os.Exit(m.Run())
}

// checkSource type-checks a single-file package and returns a fresh
// emitter over it plus the package scope.
func checkSource(t *testing.T, src string) (*emitter, *types.Package) {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "main.go", src, 0)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info := &types.Info{
		Types: map[ast.Expr]types.TypeAndValue{},
		Defs:  map[*ast.Ident]types.Object{},
		Uses:  map[*ast.Ident]types.Object{},
	}
	conf := types.Config{Importer: importer.Default()}
	pkg, err := conf.Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatalf("type-check: %v", err)
	}
	return &emitter{fset: fset, info: info, pkg: pkg}, pkg
}

const monoTestSrc = `package main

type Pair[T any] struct{ a, b T }
type Inner struct{ n int }
type Vec[T any] []T
type keyPair[A comparable, B comparable] struct {
	a A
	b B
}

var p1 Pair[int]
var p2 Pair[Inner]
var p3 Pair[*Inner]
var p4 Pair[Pair[int]]
var k1 keyPair[int, string]
var v1 Vec[byte]
var v2 Vec[rune]
var v3 Vec[any]
var v4 Vec[func(int, string) (int, error)]
var v5 Vec[func(...int) int]
var v6 Vec[map[string]Inner]
var v7 Vec[[2]Inner]
var v8 Vec[Vec[byte]]
var v9 Vec[error]
var v10 Vec[uint8]

func main() {}
`

// namedVar fetches the declared type of a package-scope variable.
func namedVar(t *testing.T, pkg *types.Package, name string) *types.Named {
	t.Helper()
	obj := pkg.Scope().Lookup(name)
	if obj == nil {
		t.Fatalf("no package-scope %s", name)
	}
	named, ok := obj.Type().(*types.Named)
	if !ok {
		t.Fatalf("%s is not a named type: %T", name, obj.Type())
	}
	return named
}

// TestInstTypeIdRenderings pins the mangled TypeId spellings against the
// design note's probe outputs: qualified origin, reflect-spelled args
// (package-NAME qualifiers, "," separators, byte→uint8, rune→int32,
// any→"interface {}", reflect func spelling).
func TestInstTypeIdRenderings(t *testing.T) {
	e, pkg := checkSource(t, monoTestSrc)
	cases := []struct {
		varName string
		want    string
	}{
		{"p1", "main.Pair[int]"},
		{"p2", "main.Pair[main.Inner]"},
		{"p3", "main.Pair[*main.Inner]"},
		{"p4", "main.Pair[main.Pair[int]]"},
		{"k1", "main.keyPair[int,string]"},
		{"v1", "main.Vec[uint8]"},
		{"v2", "main.Vec[int32]"},
		{"v3", "main.Vec[interface {}]"},
		{"v4", "main.Vec[func(int, string) (int, error)]"},
		{"v5", "main.Vec[func(...int) int]"},
		{"v6", "main.Vec[map[string]main.Inner]"},
		{"v7", "main.Vec[[2]main.Inner]"},
		{"v8", "main.Vec[main.Vec[uint8]]"},
		{"v9", "main.Vec[error]"},
	}
	for _, c := range cases {
		got, err := e.instTypeId(namedVar(t, pkg, c.varName))
		if err != nil {
			t.Errorf("%s: %v", c.varName, err)
			continue
		}
		if got != c.want {
			t.Errorf("%s: got %q, want %q", c.varName, got, c.want)
		}
	}
}

// TestByteUint8ShareKey: byte- and uint8-instantiations are ONE Go type
// (types.Identical), so the shared key must register cleanly, not trip
// the collision check.
func TestByteUint8ShareKey(t *testing.T) {
	e, pkg := checkSource(t, monoTestSrc)
	kByte, err := e.instTypeId(namedVar(t, pkg, "v1"))
	if err != nil {
		t.Fatalf("v1: %v", err)
	}
	kUint8, err := e.instTypeId(namedVar(t, pkg, "v10"))
	if err != nil {
		t.Fatalf("v10: %v", err)
	}
	if kByte != kUint8 {
		t.Fatalf("byte/uint8 instantiations render distinct keys: %q vs %q", kByte, kUint8)
	}
}

// TestMangledKeyCollisionRefuses: one key naming two non-Identical types
// must refuse the export (the belt-and-suspenders check; a legitimate
// program can never reach it — the injectivity argument — so any firing
// is a mangler bug surfacing loudly).
func TestMangledKeyCollisionRefuses(t *testing.T) {
	e, pkg := checkSource(t, monoTestSrc)
	if err := e.registerMangledKey("main.Pair[int]", namedVar(t, pkg, "p1")); err != nil {
		t.Fatalf("first registration: %v", err)
	}
	// Re-registration of the same (Identical) type is fine.
	if err := e.registerMangledKey("main.Pair[int]", namedVar(t, pkg, "p1")); err != nil {
		t.Fatalf("identical re-registration: %v", err)
	}
	err := e.registerMangledKey("main.Pair[int]", namedVar(t, pkg, "p2"))
	if err == nil {
		t.Fatalf("collision registered silently")
	}
	if _, ok := err.(unsupported); !ok {
		t.Fatalf("collision error is not the fail-closed unsupported type: %T", err)
	}
}

// TestRegistryCapRefuses: exceeding monoRegistryCap distinct keys fails
// loudly (decision §9.4 — defense in depth behind go/types' finiteness
// guarantee; never silent truncation).
func TestRegistryCapRefuses(t *testing.T) {
	e, pkg := checkSource(t, monoTestSrc)
	ty := namedVar(t, pkg, "p1")
	for i := 0; i < monoRegistryCap; i++ {
		if err := e.registerMangledKey("synthetic["+strconv.Itoa(i)+"]", ty); err != nil {
			t.Fatalf("registration %d refused below the cap: %v", i, err)
		}
	}
	if err := e.registerMangledKey("synthetic[overflow]", ty); err == nil {
		t.Fatalf("registration beyond the cap succeeded")
	}
}

// TestInstFuncIdRenderings pins instantiated-function FuncIds: bare
// declared name + bracketed args (§3.2).
func TestInstFuncIdRenderings(t *testing.T) {
	e, pkg := checkSource(t, monoTestSrc)
	intTy := types.Typ[types.Int]
	strTy := types.Typ[types.String]
	inner := namedVar(t, pkg, "p2").TypeArgs().At(0)
	got, err := e.instFuncId("genericAdd", []types.Type{intTy})
	if err != nil || got != "genericAdd[int]" {
		t.Errorf("genericAdd[int]: got %q, err %v", got, err)
	}
	got, err = e.instFuncId("hoiFirst", []types.Type{intTy, strTy})
	if err != nil || got != "hoiFirst[int,string]" {
		t.Errorf("hoiFirst[int,string]: got %q, err %v", got, err)
	}
	got, err = e.instFuncId("mk", []types.Type{types.NewPointer(inner)})
	if err != nil || got != "mk[*main.Inner]" {
		t.Errorf("mk[*main.Inner]: got %q, err %v", got, err)
	}
	// The canonical EMPTY struct is admitted (audit response m4; reflect
	// probe 2026-08-05: Bx[struct{}] names as "Bx[struct {}]").
	got, err = e.instFuncId("esId", []types.Type{types.NewStruct(nil, nil)})
	if err != nil || got != "esId[struct {}]" {
		t.Errorf("esId[struct {}]: got %q, err %v", got, err)
	}
}

// TestLocalTypeArgumentRefuses (audit response M3): a FUNCTION-LOCAL
// defined type as a type argument refuses — gc names these with a
// compiler-internal globally-unique suffix (main.score·1) that a bare
// pkg.Name key can neither reproduce nor keep injective.
func TestLocalTypeArgumentRefuses(t *testing.T) {
	src := `package main

func withLocal() any {
	type score int
	var s score = 4
	return s
}

func main() { _ = withLocal() }
`
	e, pkg := checkSource(t, src)
	var local *types.Named
	for _, obj := range collectTypeNames(e) {
		if obj.Name() == "score" {
			local = obj.Type().(*types.Named)
		}
	}
	if local == nil {
		t.Fatalf("no local type score in Defs")
	}
	if _, err := e.instFuncId("f", []types.Type{local}); err == nil {
		t.Fatalf("function-local defined type mangled instead of refusing")
	}
	_ = pkg
}

// TestLocalTypeCollisionWouldBeCaught (audit response M3): had local
// types been admitted, two same-named locals from different functions
// would render one key — the belt-and-suspenders registry refuses that
// pair LOUD (types.Identical is false for distinct declarations). The
// refusal in renderTypeArg prevents even the single-type divergence the
// registry cannot see.
func TestLocalTypeCollisionWouldBeCaught(t *testing.T) {
	src := `package main

func first() any {
	type score int
	var s score = 1
	return s
}

func second() any {
	type score int
	var s score = 2
	return s
}

func main() { _, _ = first(), second() }
`
	e, _ := checkSource(t, src)
	locals := []*types.Named{}
	for _, obj := range collectTypeNames(e) {
		if obj.Name() == "score" {
			locals = append(locals, obj.Type().(*types.Named))
		}
	}
	if len(locals) != 2 {
		t.Fatalf("expected 2 local score types, got %d", len(locals))
	}
	if types.Identical(locals[0], locals[1]) {
		t.Fatalf("distinct local declarations reported Identical")
	}
	if err := e.registerMangledKey("main.score", locals[0]); err != nil {
		t.Fatalf("first registration: %v", err)
	}
	if err := e.registerMangledKey("main.score", locals[1]); err == nil {
		t.Fatalf("same-named distinct local types shared a key silently")
	}
}

// TestRollbackUndoesInterfaceNotes (delta-review R1): interface and
// dispatch-target registrations made past a quarantine mark roll back —
// and a re-note of a PRE-existing name is not journaled, so rollback
// never deletes an entry a successful declaration also owns (the
// order-sensitivity the review verified, as a standing assertion).
func TestRollbackUndoesInterfaceNotes(t *testing.T) {
	e, _ := checkSource(t, monoTestSrc)
	iface := types.NewInterfaceType(nil, nil)
	iface.Complete()
	e.noteInterface("main.Pre", iface)
	m := e.markMono()
	e.noteInterface("main.Pre", iface) // re-note: must not be journaled
	e.noteInterface("main.Fresh", iface)
	e.noteCalledIfaceMethod("main.Fresh.M", calledIfaceMethod{ifaceName: "main.Fresh", method: "M"})
	e.rollbackMono(m)
	if _, ok := e.seenInterfaces["main.Pre"]; !ok {
		t.Errorf("pre-existing interface note deleted by rollback")
	}
	if _, ok := e.seenInterfaces["main.Fresh"]; ok {
		t.Errorf("quarantine-scoped interface note survived rollback")
	}
	if _, ok := e.calledIfaceMethods["main.Fresh.M"]; ok {
		t.Errorf("quarantine-scoped dispatch record survived rollback")
	}
}

// collectTypeNames returns every *types.TypeName in info.Defs.
func collectTypeNames(e *emitter) []*types.TypeName {
	out := []*types.TypeName{}
	for _, obj := range e.info.Defs {
		if tn, ok := obj.(*types.TypeName); ok {
			out = append(out, tn)
		}
	}
	return out
}

// TestManglingSurfaceFailsClosed: type arguments outside the admitted
// surface refuse with an unsupported error (never a silent spelling).
func TestManglingSurfaceFailsClosed(t *testing.T) {
	e, pkg := checkSource(t, monoTestSrc)
	inner := namedVar(t, pkg, "p2").TypeArgs().At(0)
	bad := []types.Type{
		types.NewChan(types.SendRecv, types.Typ[types.Int]),
		types.NewStruct([]*types.Var{types.NewField(token.NoPos, pkg, "x", types.Typ[types.Int], false)}, nil),
	}
	for _, b := range bad {
		if _, err := e.instFuncId("f", []types.Type{b}); err == nil {
			t.Errorf("type argument %s mangled instead of refusing", b)
		}
	}
	// The qualifier machinery still records packages for the collision
	// gate: rendering an Inner-argument key registers "main"'s path.
	if _, err := e.instFuncId("f", []types.Type{inner}); err != nil {
		t.Fatalf("inner: %v", err)
	}
	if len(e.qualPkgPaths["main"]) == 0 {
		t.Errorf("type-argument rendering did not record the package qualifier for the collision gate")
	}
}
