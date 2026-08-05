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
	"strconv"
	"testing"
)

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
