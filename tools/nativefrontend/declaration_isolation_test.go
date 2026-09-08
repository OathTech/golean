package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

func declarationSource(t *testing.T, src string) (*emitter, []*ast.File) {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "main.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	info := newTypesInfo()
	pkg, err := (&types.Config{Importer: importer.Default()}).Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatal(err)
	}
	return &emitter{fset: fset, info: info, pkg: pkg}, []*ast.File{f}
}

func TestDeclarationQueryIsolation(t *testing.T) {
	const src = `package main
type Named bool
var n Named
func f() { type Local bool; var local Local; _ = local }
func main() { f(); println(n) }
`
	queries := []struct {
		name      string
		query     func(*emitter) types.Type
		wantError string
	}{
		{"named", func(e *emitter) types.Type { return varType(t, e, "n") }, ""},
		{"local", func(e *emitter) types.Type { return varType(t, e, "local") }, ""},
		{"foreign-local", func(e *emitter) types.Type {
			pkg := types.NewPackage("foreign", "foreign")
			return types.NewNamed(types.NewTypeName(token.NoPos, pkg, "Missing", nil), types.Typ[types.Bool], nil)
		}, "no local type ordinal"},
		{"foreign-package", func(e *emitter) types.Type {
			pkg := types.NewPackage("example.org/foreign", "foreign")
			obj := types.NewTypeName(token.NoPos, pkg, "Named", nil)
			pkg.Scope().Insert(obj)
			return types.NewNamed(obj, types.Typ[types.Bool], nil)
		}, ""},
	}
	for _, q := range queries {
		t.Run(q.name, func(t *testing.T) {
			plain, plainFiles := declarationSource(t, src)
			want, err := plain.emitProgram(plainFiles)
			if err != nil {
				t.Fatal(err)
			}
			wantBytes, err := json.Marshal(want)
			if err != nil {
				t.Fatal(err)
			}
			queried, files := declarationSource(t, src)
			// Seed registries as well as testing their nil state: a shallow
			// copy would otherwise appear isolated when it lazily allocates.
			queried.typeDisplays = map[string]typeDisplay{"kept": {display: "kept"}}
			queried.badKeyPaths = map[string]string{}
			queried.badLocalTypes = map[string]bool{}
			before := fmt.Sprintf("%#v", *queried)
			value, queryErr := queried.emitDeclarationType(q.query(queried))
			if q.wantError == "" {
				if queryErr != nil || value == nil {
					t.Fatalf("query: %v / %v", value, queryErr)
				}
			} else if queryErr == nil || !strings.Contains(queryErr.Error(), q.wantError) || value != nil {
				t.Fatalf("expected %q refusal, got %v / %v", q.wantError, value, queryErr)
			}
			if after := fmt.Sprintf("%#v", *queried); after != before {
				t.Errorf("declaration query mutated executable-emitter state")
			}
			got, err := queried.emitProgram(files)
			if err != nil {
				t.Fatalf("query poisoned executable emission: %v", err)
			}
			gotBytes, err := json.Marshal(got)
			if err != nil {
				t.Fatal(err)
			}
			if !bytes.Equal(gotBytes, wantBytes) {
				t.Fatal("executable wire changed after declaration query")
			}
		})
	}
}

func TestDeclarationMissingPackageBoundary(t *testing.T) {
	e := &emitter{}
	// A real predeclared nominal has no package. A fabricated object with
	// the same spelling must not acquire that identity.
	universe := types.Universe.Lookup("error")
	if got := declarationJSON(t, e, universe.Type()); got != `{"args":[],"id":"error","kind":"named"}` {
		t.Fatalf("predeclared error changed: %s", got)
	}
	for _, name := range []string{"error", "Invented"} {
		bad := types.NewNamed(types.NewTypeName(token.NoPos, nil, name, nil), types.Typ[types.Bool], nil)
		if value, err := e.emitDeclarationType(bad); err == nil || !strings.Contains(err.Error(), "package") || value != nil {
			t.Errorf("package-less nominal %s accepted: %v / %v", name, value, err)
		}
	}
	field := types.NewStruct([]*types.Var{types.NewField(token.NoPos, nil, "hidden", types.Typ[types.Bool], false)}, nil)
	method := types.NewInterfaceType([]*types.Func{types.NewFunc(token.NoPos, nil, "hidden",
		types.NewSignatureType(nil, nil, nil, nil, nil, false))}, nil).Complete()
	for _, bad := range []types.Type{field, method} {
		if value, err := e.emitDeclarationType(bad); err == nil || !strings.Contains(err.Error(), "package") || value != nil {
			t.Errorf("private member without package accepted: %v / %v", value, err)
		}
	}
}

func TestDeclarationStencilIsolation(t *testing.T) {
	e, files := declarationSource(t, `package main
type Seq[T any] func(T)
func generic[T any]() { type Local bool; var local Local; _ = local }
func main() {}
`)
	parameter := e.pkg.Scope().Lookup("generic").Type().(*types.Signature).TypeParams().At(0)
	e.curSubst = map[*types.TypeParam]types.Type{parameter: types.Typ[types.Bool]}
	for _, decl := range files[0].Decls {
		if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.Name == "generic" {
			e.curInstDecl = fn
		}
	}
	origin := e.pkg.Scope().Lookup("Seq").Type().(*types.Named)
	seqBool, err := types.Instantiate(types.NewContext(), origin, []types.Type{types.Typ[types.Bool]}, true)
	if err != nil {
		t.Fatal(err)
	}
	seqParam, err := types.Instantiate(types.NewContext(), origin, []types.Type{parameter}, false)
	if err != nil {
		t.Fatal(err)
	}
	e.curTargs = []types.Type{seqBool}
	// Existing cache/registry objects must not be borrowed by the query.
	e.monoCtxt = types.NewContext()
	e.mangledKeys = map[string]types.Type{"kept": types.Typ[types.Bool]}
	e.typeDisplays = map[string]typeDisplay{"kept": {display: "kept"}}
	e.monoLog = make([]monoLogEntry, 0, 8)
	check := func(ty types.Type, want, refusal string) {
		t.Helper()
		before := fmt.Sprintf("%#v", *e)
		value, err := e.emitDeclarationType(ty)
		if refusal == "" {
			if err != nil {
				t.Fatal(err)
			}
			data, err := json.Marshal(value)
			if err != nil {
				t.Fatal(err)
			}
			if string(data) != want {
				t.Fatalf("substitution identity: %s, want %s", data, want)
			}
		} else if err == nil || !strings.Contains(err.Error(), refusal) || value != nil {
			t.Fatalf("expected %q refusal, got %v / %v", refusal, value, err)
		}
		if fmt.Sprintf("%#v", *e) != before {
			t.Fatal("stencil query mutated executable-emitter state")
		}
	}
	check(types.NewPointer(parameter), `{"elem":{"basic":"bool","kind":"basic"},"kind":"pointer"}`, "")
	check(seqParam, `{"args":[{"basic":"bool","kind":"basic"}],"id":"main.Seq","kind":"named"}`, "")
	check(varType(t, e, "local"), `{"args":[],"id":"main.Local·1[main.Seq[bool]]","kind":"named"}`, "")
	unbound := types.NewTypeParam(types.NewTypeName(token.NoPos, nil, "Unbound", nil),
		types.NewInterfaceType(nil, nil).Complete())
	check(types.NewPointer(unbound), "", "unbound type parameter")
	e.curTargs = []types.Type{types.NewChan(types.SendRecv, types.Typ[types.Bool])}
	check(varType(t, e, "local"), "", "outside the mangling surface")
}
