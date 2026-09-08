package main

import (
	"encoding/json"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

func declarationJSON(t *testing.T, e *emitter, ty types.Type) string {
	t.Helper()
	decl, err := e.emitDeclarationType(ty)
	if err != nil {
		t.Fatal(err)
	}
	data, err := json.Marshal(decl)
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

// Compare the new declaration identity with go/types, including cases for
// which the executable emitter cannot provide a value representation.
func TestDeclarationIdentityAgainstGoTypes(t *testing.T) {
	e, _ := checkSource(t, `package main
type Named complex128
type Alias = complex128
type Seq[T any] func(T)
var (
 c complex128; a Alias; n Named; small complex64
 i Seq[int]; i2 Seq[int]; b Seq[bool]
 f func(x int, rest ...string) (r bool)
 f2 func(int, ...string) bool
 slice func(int, []string) bool
 send chan<- bool; recv <-chan bool; both chan bool
 s1 struct { X int "a" }; s2 struct { X int "b" }
 m1 interface { Z(); A(complex128) bool }
 m2 interface { A(complex128) bool; Z() }
 arr1 [1]complex128; arr2 [2]complex128
 byteAlias byte; byteBase uint8; runeAlias rune; runeBase int32
)
func main() {}
`)
	pairs := [][2]string{{"c", "a"}, {"c", "n"}, {"c", "small"},
		{"i", "i2"}, {"i", "b"}, {"f", "f2"}, {"f", "slice"},
		{"send", "recv"}, {"send", "both"}, {"s1", "s2"},
		{"m1", "m2"}, {"arr1", "arr2"}, {"byteAlias", "byteBase"},
		{"runeAlias", "runeBase"}}
	for _, pair := range pairs {
		left, right := varType(t, e, pair[0]), varType(t, e, pair[1])
		want := types.Identical(left, right)
		got := declarationJSON(t, e, left) == declarationJSON(t, e, right)
		if got != want {
			t.Errorf("%v: declaration equality %v, go/types %v", pair, got, want)
		}
	}
	if got := declarationJSON(t, e, varType(t, e, "c")); got != `{"basic":"complex128","kind":"basic"}` {
		t.Fatalf("complex identity was not a positive basic type: %s", got)
	}
	if len(e.opaqueBasics) != 0 || len(e.opaqueInsts) != 0 {
		t.Fatal("declaration serialization registered executable opaque markers")
	}
}

func TestDeclarationUnexportedIdentityAndTags(t *testing.T) {
	e := &emitter{}
	p, q := types.NewPackage("example.org/p", "same"), types.NewPackage("example.org/q", "same")
	structure := func(pkg *types.Package, name, tag string) *types.Struct {
		return types.NewStruct([]*types.Var{types.NewField(token.NoPos, pkg, name, types.Typ[types.Int], false)}, []string{tag})
	}
	for _, name := range []string{"x", "X", "_"} {
		left, right := structure(p, name, ""), structure(q, name, "")
		if got, want := declarationJSON(t, e, left) == declarationJSON(t, e, right), types.Identical(left, right); got != want {
			t.Errorf("field %s: declaration equality %v, go/types %v", name, got, want)
		}
	}
	invalid, replacement := structure(p, "X", "\xff"), structure(p, "X", "\xef\xbf\xbd")
	if declarationJSON(t, e, invalid) == declarationJSON(t, e, replacement) {
		t.Fatal("JSON replaced a tag byte and merged distinct struct identities")
	}
	if got := declarationJSON(t, e, invalid); !strings.Contains(got, `"tagBytes":[255]`) {
		t.Fatalf("invalid UTF-8 tag did not retain its exact byte: %s", got)
	}
	methodSet := func(pkg *types.Package, name string) *types.Interface {
		sig := types.NewSignatureType(nil, nil, nil, types.NewTuple(), types.NewTuple(), false)
		method := types.NewFunc(token.NoPos, pkg, name, sig)
		return types.NewInterfaceType([]*types.Func{method}, nil).Complete()
	}
	for _, name := range []string{"m", "M"} {
		left, right := methodSet(p, name), methodSet(q, name)
		if got, want := declarationJSON(t, e, left) == declarationJSON(t, e, right), types.Identical(left, right); got != want {
			t.Errorf("method %s: declaration equality %v, go/types %v", name, got, want)
		}
	}
}

func TestDeclarationClosedTypeBoundary(t *testing.T) {
	e := &emitter{}
	parameter := types.NewTypeParam(types.NewTypeName(token.NoPos, nil, "T", nil), types.NewInterfaceType(nil, nil).Complete())
	for _, ty := range []types.Type{types.Typ[types.Invalid], types.Typ[types.UntypedInt], parameter,
		types.NewPointer(parameter), types.NewSlice(parameter), types.NewArray(parameter, 2),
		types.NewMap(types.Typ[types.Int], parameter), types.NewChan(types.SendRecv, parameter),
		types.NewArray(types.Typ[types.Bool], -1), types.NewChan(types.ChanDir(99), types.Typ[types.Bool])} {
		if decl, err := e.emitDeclarationType(ty); err == nil || decl != nil {
			t.Errorf("non-closed type %s produced declaration %v / error %v", ty, decl, err)
		}
	}
	constraint := types.NewInterfaceType(nil, []types.Type{types.NewUnion([]*types.Term{
		types.NewTerm(true, types.Typ[types.Int]),
	})}).Complete()
	if decl, err := e.emitDeclarationType(constraint); err == nil || decl != nil {
		t.Fatalf("constraint-only interface admitted as a runtime declaration: %v / %v", decl, err)
	}
	if got := declarationJSON(t, e, types.Typ[types.UnsafePointer]); got != `{"basic":"unsafe.Pointer","kind":"basic"}` {
		t.Fatalf("unsafe.Pointer identity is not positive: %s", got)
	}
}

func TestDeclarationImportedAndLocalNominalTypes(t *testing.T) {
	e, _ := checkSource(t, `package main
import "iter"
var seq iter.Seq[int]
var seq2 iter.Seq[bool]
func one() { type Local bool; var first Local; _ = first }
func two() { type Local bool; var second Local; _ = second }
func main() {}
`)
	got := declarationJSON(t, e, varType(t, e, "seq"))
	if got != `{"args":[{"basic":"int","kind":"basic"}],"id":"iter.Seq","kind":"named"}` {
		t.Fatalf("imported instance lost its declaration or argument identity: %s", got)
	}
	if got == declarationJSON(t, e, varType(t, e, "seq2")) {
		t.Fatal("imported instantiation arguments collapsed")
	}
	if declarationJSON(t, e, varType(t, e, "first")) == declarationJSON(t, e, varType(t, e, "second")) {
		t.Fatal("distinct local declarations collapsed")
	}
	// A foreign local object absent from the source inventory must not emit
	// qualifiedTypeName's diagnostic placeholder as a positive declaration.
	foreign := types.NewPackage("other", "other")
	obj := types.NewTypeName(token.NoPos, foreign, "Local", nil)
	named := types.NewNamed(obj, types.Typ[types.Bool], nil)
	if decl, err := e.emitDeclarationType(named); err == nil || decl != nil {
		t.Fatalf("unknown local identity escaped as declaration %v / %v", decl, err)
	}
	if len(e.opaqueBasics) != 0 || len(e.opaqueInsts) != 0 {
		t.Fatal("signature identities registered opaque executable types")
	}
}

func TestDeclarationNamedConstraintBoundary(t *testing.T) {
	e, _ := checkSource(t, `package main
type Constraint interface { ~int }
type Alias = Constraint
type Methods interface { M() }
type Empty interface {}
func main() {}
`)
	for _, ty := range []types.Type{
		types.Universe.Lookup("comparable").Type(),
		e.pkg.Scope().Lookup("Constraint").Type(),
		e.pkg.Scope().Lookup("Alias").Type(),
		types.NewPointer(e.pkg.Scope().Lookup("Constraint").Type()),
	} {
		value, err := e.emitDeclarationType(ty)
		if value != nil || err == nil || !strings.Contains(err.Error(), "non-method type-set terms") {
			t.Errorf("constraint-only declaration %s: %v / %v", ty, value, err)
		}
	}
	for _, ty := range []types.Type{
		types.Universe.Lookup("error").Type(),
		e.pkg.Scope().Lookup("Methods").Type(),
		e.pkg.Scope().Lookup("Empty").Type(),
	} {
		if value, err := e.emitDeclarationType(ty); value == nil || err != nil {
			t.Errorf("runtime interface declaration %s refused: %v", ty, err)
		}
	}
}
