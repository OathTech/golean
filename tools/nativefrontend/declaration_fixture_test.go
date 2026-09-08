package main

import (
	"encoding/json"
	"go/types"
	"os"
	"testing"
)

// The dedicated Lean decoder gate requests this exact producer output. The
// ordinary unit suite still checks every identity pair when no output path is
// supplied; producing the cross-language artifact is not a conformance claim.
func TestDeclarationDecoderFixture(t *testing.T) {
	e, _ := checkSource(t, `package main
import "unsafe"
type Alias = complex128
type Named complex128
type Seq[T any] func(T)
type Recursive struct { Next *Recursive }
var (
 b bool; n int; u uint; up uintptr; unsafePtr unsafe.Pointer
 c complex128; alias Alias; small complex64; named Named
 i Seq[int]; i2 Seq[int]; ib Seq[bool]; rec Recursive
 f func(x string, rest ...complex128) bool
 f2 func(string, ...complex128) bool
 f3 func(string, []complex128) bool
 m1 interface { Z(); A(complex128) bool }
 m2 interface { A(complex128) bool; Z() }
 s1 struct { X bool "\xff" }; s2 struct { X bool "\ufffd" }
 send chan<- bool; recv <-chan bool; both chan bool
 arr [2]map[string]*Recursive
)
func main() {}
`)
	names := []string{"b", "n", "u", "up", "unsafePtr", "c", "alias", "small", "named",
		"i", "i2", "ib", "rec", "f", "f2", "f3", "m1", "m2", "s1", "s2", "send", "recv", "both", "arr"}
	rows := make([]any, len(names))
	wires := make([]any, len(names))
	for i, name := range names {
		wire, err := e.emitDeclarationType(varType(t, e, name))
		if err != nil {
			t.Fatal(err)
		}
		wires[i] = wire
		rows[i] = map[string]any{"name": name, "type": wire}
	}
	var pairs []any
	for i, a := range names {
		for j, b := range names {
			want := types.Identical(varType(t, e, a), varType(t, e, b))
			left, err := json.Marshal(wires[i])
			if err != nil {
				t.Fatal(err)
			}
			right, err := json.Marshal(wires[j])
			if err != nil {
				t.Fatal(err)
			}
			if got := string(left) == string(right); got != want {
				t.Fatalf("serializer equality disagrees with go/types: %s / %s", a, b)
			}
			pairs = append(pairs, map[string]any{"left": i, "right": j, "equal": want})
		}
	}
	var nominals []any
	for _, name := range []string{"Named", "Seq", "Recursive"} {
		obj := e.pkg.Scope().Lookup(name).(*types.TypeName)
		named := obj.Type().(*types.Named)
		nominals = append(nominals, map[string]any{"id": e.qualifiedTypeName(obj), "arity": named.TypeParams().Len()})
	}
	data, err := json.MarshalIndent(map[string]any{"schema": "i1-declaration-test-v1", "nominals": nominals,
		"types": rows, "pairs": pairs}, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	if output := os.Getenv("GOLEAN_DECLARATION_FIXTURE"); output != "" {
		if err := os.WriteFile(output, append(data, '\n'), 0600); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("checked %d declaration identities and %d go/types equality pairs", len(names), len(pairs))
}
