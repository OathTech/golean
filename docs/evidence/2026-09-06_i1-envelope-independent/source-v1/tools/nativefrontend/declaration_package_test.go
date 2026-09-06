package main

import (
	"bytes"
	"encoding/json"
	"go/types"
	"os"
	"path/filepath"
	"testing"
)

var declarationPackageSources = []struct{ name, source string }{
	{"source", `package main
type R struct{}
func (R) M(xs ...complex128) complex128 { return 0 }
type Wrapper struct { R }
type I interface { M(...complex128) complex128 }
type Box[T any] struct { X T }
func (b Box[T]) Echo(x T) T { return x }
type UnusedOrigin[A, B any] struct { A A; B B }
var Global int = 2
func F(x complex128) complex128 { return x }
func G(y complex128) complex128 { return y }
func H(x complex64) complex64 { return x }
func Variadic(xs ...complex128) complex128 { return 0 }
func Tagged(x struct { X int "\xff" }) bool { return true }
func Closure(seed int) int { f := func(xs ...int) int { return seed + len(xs) }; return f(2) }
func Phantom[T any]() bool { return true }
func UseGeneric() bool { var b Box[bool]; return b.Echo(Phantom[int]()) }
func Query(r R) bool { _, ok := any(r).(I); return ok }
func main() {}
`},
	{"imported", `package main
import "reflect"
func Inspect(v reflect.Value) bool { return true }
func main() {}
`},
	{"sync", `package main
import "sync"
func Synchronize() { var once sync.Once; once.Do(func() {}); var mu sync.Mutex; mu.Lock(); defer mu.Unlock(); defer recover(); ch := make(chan int); defer close(ch) }
func main() {}
`},
	{"format", `package main
import "fmt"
type Text int
func (Text) String() string { return "text" }
type Record struct { N int }
func Format() string { return fmt.Sprintf("%v %d %v", Text(1), 3, []Record{{N: 1}}) }
func main() {}
`},
	{"atomic", `package main
import "sync/atomic"
func Atomic() int32 { var n atomic.Int32; n.Store(4); return n.Load() }
func main() {}
`},
}

// This gate must exercise the real pinned loader, shims, worklists, model
// harvest and final emitter. A missing source pin is a failure, not a skip.
// All source/program/query artifacts live in a caller-owned unique directory.
func TestDeclarationPackageFixture(t *testing.T) {
	savedRoot, savedPin := stdlibSrcRoot, stdlibPinPath
	stdlibSrcRoot = filepath.Join("..", "..", "deps", "go", "src")
	stdlibPinPath = filepath.Join("..", "..", "baselines", "stdlib-pin.tsv")
	t.Cleanup(func() { stdlibSrcRoot, stdlibPinPath = savedRoot, savedPin })
	if err := checkStdlibSrcRev(); err != nil {
		t.Fatal(err)
	}
	root := os.Getenv("GOLEAN_DECLARATION_PACKAGE_FIXTURE")
	if root == "" {
		var err error
		root, err = os.MkdirTemp(filepath.Join("..", "..", ".tmp"), "declaration-package-")
		if err != nil {
			t.Fatal(err)
		}
	}
	if err := os.MkdirAll(root, 0o755); err != nil {
		t.Fatal(err)
	}
	write := func(path string, value any) {
		t.Helper()
		b, err := json.MarshalIndent(value, "", " ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, b, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	manifest := []any{}
	for _, fixture := range declarationPackageSources {
		t.Run(fixture.name, func(t *testing.T) {
			dir := filepath.Join(root, fixture.name)
			if err := os.MkdirAll(dir, 0o755); err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(fixture.source), 0o644); err != nil {
				t.Fatal(err)
			}
			program, err := lowerProgramDir(t, dir)
			if err != nil {
				t.Fatal(err)
			}
			encoded, err := json.Marshal(program)
			if err != nil || bytes.Contains(encoded, []byte(`"$declaration"`)) {
				t.Fatalf("private declaration payload leaked: %v", err)
			}
			env := program["declarations"].(map[string]any)
			for _, table := range []string{"funcs", "methods"} {
				if len(program[table].([]any)) != len(env[table].([]any)) {
					t.Fatalf("%s declaration inventory differs", table)
				}
			}
			queries := []any{}
			if fixture.name == "source" {
				_, pkg := checkSource(t, fixture.source)
				names := []string{"F", "G", "H", "Variadic"}
				for _, a := range names {
					for _, b := range names {
						queries = append(queries, map[string]any{"left": a, "right": b,
							"equal": types.Identical(pkg.Scope().Lookup(a).Type(), pkg.Scope().Lookup(b).Type())})
					}
				}
				// Independently inventory all source-scope origins, including the
				// unused generic origin. No envelope-derived arity is an oracle.
				for _, name := range pkg.Scope().Names() {
					obj, ok := pkg.Scope().Lookup(name).(*types.TypeName)
					if !ok || obj.IsAlias() {
						continue
					}
					named := obj.Type().(*types.Named)
					queries = append(queries, map[string]any{"nominal": pkg.Path() + "." + obj.Name(),
						"arity": named.Origin().TypeParams().Len()})
				}
				for _, name := range []string{"R", "Wrapper"} {
					receiver := pkg.Scope().Lookup(name).Type()
					selection := types.NewMethodSet(receiver).Lookup(nil, "M")
					if selection == nil {
						t.Fatal("source method query has no actual Go method")
					}
					declaring := selection.Obj().Type().(*types.Signature).Recv().Type().(*types.Named).Obj()
					queries = append(queries, map[string]any{"method": "main." + name + ".M",
						"receiver": pkg.Path() + "." + name,
						"declaringReceiver": declaring.Pkg().Path() + "." + declaring.Name(),
						"interface": "main.I", "satisfies": types.Implements(receiver,
							pkg.Scope().Lookup("I").Type().Underlying().(*types.Interface))})
				}
			}
			write(filepath.Join(dir, "program.json"), program)
			write(filepath.Join(dir, "queries.json"), queries)
			manifest = append(manifest, map[string]any{"name": fixture.name,
				"functions": len(env["funcs"].([]any)), "methods": len(env["methods"].([]any)),
				"nominals": len(env["nominals"].([]any)), "interfaces": len(env["interfaces"].([]any)),
				"queries": len(queries)})
			t.Logf("%s: %d functions, %d methods; source and whole program retained at %s",
				fixture.name, len(env["funcs"].([]any)), len(env["methods"].([]any)), dir)
		})
	}
	write(filepath.Join(root, "manifest.json"), manifest)
	t.Logf("actual package declaration fixtures retained: %s", root)
}
