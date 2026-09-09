package main

import (
	"encoding/json"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"strings"
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
	t.Run("refusal-display", checkMethodRefusalDisplay)
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

// Cross-language vector pinned by Tests.MethodIdentity.utf8_target_vector.
func TestMethodFuncKey(t *testing.T) {
	if got := methodFuncKey("main.Δ", memberID{Name: "é", Package: "p"}); got != "$method$7:main.Δ1:pé" {
		t.Fatalf("UTF-8 target vector: %q", got)
	}
	seen := map[string]string{}
	for _, recv := range []string{"main.Mix", "main.Δ", "r:1", "r1:", "r"} {
		for _, id := range []memberID{{Name: "m", Package: "red/inner"}, {Name: "m", Package: "blue/inner"}, {Name: "é", Package: "p"}, {Name: "É"}, {Name: "𐐀"}, {Name: "m", Package: "1:p"}} {
			label := recv + " / " + id.Package + " / " + id.Name
			key := methodFuncKey(recv, id)
			if old, ok := seen[key]; ok {
				t.Fatalf("target collision %s / %s", old, label)
			}
			seen[key] = label
		}
	}
}

// [AGENT] Init reachability is conservative over receiver/signature but exact
// over private member identity: an unrelated private method cannot poison it.
func TestInitQuarantinePreservesMemberIdentity(t *testing.T) {
	p := memberID{Name: "m", Package: "red/inner"}
	q := memberID{Name: "m", Package: "blue/inner"}
	body := map[string]any{"stmt": "block", "body": []any{}}
	for _, anchorMember := range []memberID{p, q} {
		anchorKey := methodFuncKey("main.I", anchorMember)
		funcs := []any{map[string]any{"name": "$pkginit", "body": map[string]any{"expr": "call", "func": anchorKey}}}
		methods := []any{
			map[string]any{"recvType": "main.I", "id": anchorMember, "interface": true},
			map[string]any{"recvType": "main.Mix", "id": p, "body": body},
			map[string]any{"recvType": "main.Mix", "id": q, "unsupported": "identity control quarantine"},
		}
		err := checkInitQuarantine(funcs, methods)
		if anchorMember == p && err != nil {
			t.Fatalf("foreign private member poisoned init: %v", err)
		}
		if anchorMember == q && (err == nil || !strings.Contains(err.Error(), "identity control quarantine")) {
			t.Fatalf("matching private quarantine did not block init: %v", err)
		}
	}
}

// [AGENT] Audit R2: fixture reasons must name declarations, while callable
// targets and lifted children keep their separate package-correct ids.
func checkMethodRefusalDisplay(t *testing.T) {
	fixtures := map[string][][2]string{
		"imported-generic-in-signature": {{"main.Bag", "All"}, {"main.Bag", "Indexed"}},
		"imported-generic-sig-calls":    {{"main.Bag", "All"}, {"main.Bag", "Sum"}},
		"stencil-quarantine-iterseq":    {{"main.set[int]", "All"}},
	}
	for fixture, methods := range fixtures {
		t.Run(fixture, func(t *testing.T) {
			program, err := lowerProgramDir(t, filepath.Join("../../Corpus/coverage/exec/generics", fixture))
			if err != nil {
				t.Fatal(err)
			}
			for _, method := range methods {
				record := findMethod(program, method[0], method[1])
				if record == nil {
					t.Fatalf("missing method %v", method)
				}
				reason, ok := record["unsupported"].(string)
				want := " in " + method[0] + "." + method[1] + " (FR-23:"
				if !ok || !strings.Contains(reason, want) || strings.Contains(reason, "$method$") {
					t.Fatalf("method display %v: want %q, got %q", method, want, reason)
				}
			}
		})
	}
}
