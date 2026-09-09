package main

import (
	"encoding/json"
	"go/token"
	"go/types"
	"os"
	"testing"
)

// Both declaration and executable wires use this checked-object constructor.
// Equal package names are deliberately backed by different import paths.
func TestMemberIdentityCheckedObjects(t *testing.T) {
	for _, name := range []string{"m", "é", "ǅ", "M", "É", "Σ", "𐐀"} {
		a, err := declarationObjectName(types.NewFunc(token.NoPos, types.NewPackage("red/inner", "inner"), name, nil))
		if err != nil {
			t.Fatal(err)
		}
		b, err := declarationObjectName(types.NewFunc(token.NoPos, types.NewPackage("blue/inner", "inner"), name, nil))
		if err != nil {
			t.Fatal(err)
		}
		exported := token.IsExported(name)
		if (a == b) != exported || a.Name != name || b.Name != name {
			t.Fatalf("member identity %q: %v / %v", name, a, b)
		}
		if exported && (a.Package != "" || b.Package != "") || !exported && (a.Package != "red/inner" || b.Package != "blue/inner") {
			t.Fatalf("wrong package provenance: %v / %v", a, b)
		}
	}
	if _, err := declarationObjectName(types.NewFunc(token.NoPos, nil, "m", nil)); err == nil {
		t.Fatal("private checked object without a package accepted")
	}
}

func TestExecutableMemberIdentityFixture(t *testing.T) {
	program, err := emitSource(t, `package main
 type T int
 func (T) m() int { return 11 }
 func (T) M() int { return 12 }
 func (T) é() int { return 13 }
 func (T) É() int { return 14 }
 func (T) ǅ() int { return 15 }
 func (T) 𐐀() int { return 16 }
 type S struct { T }
 type I interface { m() int; M() int; é() int; É() int; ǅ() int; 𐐀() int }
 func call(x I) int { return x.m() }
 func errText(e error) string { return e.Error() }
 func main() { println(call(S{})) }
 `)
	if err != nil {
		t.Fatal(err)
	}
	for _, recv := range []string{"main.T", "main.S", "main.I"} {
		for _, name := range []string{"m", "M", "é", "É", "ǅ", "𐐀"} {
			record := findMethod(program, recv, name)
			if record == nil {
				t.Fatalf("missing %s.%s", recv, name)
			}
			wantPkg := "main"
			if token.IsExported(name) {
				wantPkg = ""
			}
			if record["id"] != (memberID{Name: name, Package: wantPkg}) {
				t.Fatalf("wrong member: %v", record["id"])
			}
			if _, legacy := record["name"]; legacy {
				t.Fatal("parallel bare method identity survived")
			}
		}
	}
	if path := os.Getenv("GOLEAN_METHOD_IDENTITY_FIXTURE"); path != "" {
		data, err := json.MarshalIndent(program, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, append(data, '\n'), 0600); err != nil {
			t.Fatal(err)
		}
	}
}
