package main

// Unit tests for the per-declaration quarantine of METHODS (H-3,
// 2026-08-19; emit.go, quarantinedMethodStub). The differential corpus
// (Corpus/coverage/exec/methods/quarantine-*) pins the OBSERVABLE contract —
// the package exports, good methods run, a call refuses. These pin the two
// things the differential structurally cannot see:
//
//  1. the stub's SIGNATURE is the real one (receiver spelling included), the
//     property interface satisfaction reads — a corpus row can only witness
//     one satisfaction question, never that the recorded signature is right;
//  2. the refusal NAMES package.Type.Method, and an un-lowerable SIGNATURE
//     fails the whole export instead of recording an incomplete method set.

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

// emitSource type-checks a single-file main package and emits the whole wire
// program, the way run() does for a real case directory.
func emitSource(t *testing.T, src string) (map[string]any, error) {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "main.go", src, 0)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info := newTypesInfo()
	conf := types.Config{Importer: importer.Default()}
	pkg, err := conf.Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatalf("type-check: %v", err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	return e.emitProgram([]*ast.File{f})
}

// findMethod returns the wire entry for recvType.name, or nil.
func findMethod(program map[string]any, recvType, name string) map[string]any {
	ms, _ := program["methods"].([]any)
	for _, m := range ms {
		mm, ok := m.(map[string]any)
		if !ok {
			continue
		}
		if mm["recvType"] == recvType && mm["name"] == name {
			return mm
		}
	}
	return nil
}

const quarantineMethodSrc = `package main

import "reflect"

type T struct{ n int }

func (t T) Good() int { return t.n + 1 }

func (t T) Bad(a int, rest ...string) (int, error) {
	// reflect.TypeOf is the quarantine cause — the THIRD pick (JC-17):
	// fmt.Sprintf lowered when the W4.1 desugar landed; fmt.Sprint
	// lowered when audit R4-M-1 modeled the fixed-arity form (the
	// previous comment's "the witnesses depend on fmt.Sprint refusing"
	// was a corpus-scoped refusal inversion — the LESSON is to pick a
	// cause by structural distance from the modeled envelope, not by
	// "currently unmodeled"). Reflection is the deep-latitude surface
	// the closed-world frontend does not model by doctrine; no eternal
	// refusal exists, but if reflect ever lowers, this test and the
	// corpus siblings go red/green LOUDLY and retarget again.
	return len(reflect.TypeOf(a).String()), nil
}

func (t *T) PtrBad() string { return reflect.TypeOf(t.n).String() }

func main() {}
`

// TestQuarantinedMethodKeepsPackageExportable is the H-3 headline: one
// unlowerable method used to refuse the WHOLE export (docs/raft-w2-log.md
// §6b). The siblings must survive it.
func TestQuarantinedMethodKeepsPackageExportable(t *testing.T) {
	program, err := emitSource(t, quarantineMethodSrc)
	if err != nil {
		t.Fatalf("export refused by a quarantinable method: %v", err)
	}
	good := findMethod(program, "main.T", "Good")
	if good == nil {
		t.Fatal("the lowerable sibling method is missing from the wire")
	}
	if _, stubbed := good["unsupported"]; stubbed {
		t.Fatal("a lowerable method was quarantined")
	}
	if good["body"] == nil {
		t.Fatal("the lowerable sibling method lost its body")
	}
}

// TestQuarantinedMethodNeverDropped is the fail-closed invariant: the entry
// stays in the method table (interface satisfaction reads it) and refuses
// only when CALLED, naming package.Type.Method.
func TestQuarantinedMethodNeverDropped(t *testing.T) {
	program, err := emitSource(t, quarantineMethodSrc)
	if err != nil {
		t.Fatalf("export: %v", err)
	}
	bad := findMethod(program, "main.T", "Bad")
	if bad == nil {
		t.Fatal("quarantined method DROPPED from the method table — " +
			"interface satisfaction would answer a silently wrong `no`")
	}
	reason, ok := bad["unsupported"].(string)
	if !ok {
		t.Fatalf("quarantined method carries no refusal reason: %v", bad)
	}
	if !strings.Contains(reason, "main.T.Bad") {
		t.Fatalf("refusal does not name package.Type.Method: %q", reason)
	}
	if !strings.Contains(reason, "reflect") {
		t.Fatalf("refusal drops the underlying cause: %q", reason)
	}
	if bad["body"] != nil {
		t.Fatalf("a quarantined method must carry NO body: %v", bad["body"])
	}
}

// TestQuarantinedMethodCarriesRealSignature: satisfiesMethodSig compares
// receiver, params, results and the variadic marker, so every one of them
// must be the declared one. A truncated signature is the silent-wrong-answer
// mode this stub shape exists to prevent.
func TestQuarantinedMethodCarriesRealSignature(t *testing.T) {
	program, err := emitSource(t, quarantineMethodSrc)
	if err != nil {
		t.Fatalf("export: %v", err)
	}
	bad := findMethod(program, "main.T", "Bad")
	if bad == nil {
		t.Fatal("no stub for main.T.Bad")
	}
	params, _ := bad["params"].([]any)
	if len(params) != 2 {
		t.Fatalf("stub params: got %d, want 2 (%v)", len(params), params)
	}
	results, _ := bad["results"].([]any)
	if len(results) != 2 {
		t.Fatalf("stub results: got %d, want 2 (%v)", len(results), results)
	}
	if variadic, _ := bad["variadic"].(bool); !variadic {
		t.Fatal("stub dropped the variadic marker: `Bad(int, ...string)` and " +
			"`Bad(int, []string)` are DIFFERENT method signatures")
	}
	// The receiver spelling decides Go's method-set asymmetry: a value stub
	// recorded for a pointer-receiver method would make the value type
	// satisfy an interface it does not satisfy.
	recv, _ := bad["recv"].(map[string]any)
	rty, _ := recv["type"].(map[string]any)
	if rty["kind"] != "named" || rty["name"] != "main.T" {
		t.Fatalf("value-receiver stub recorded receiver %v", rty)
	}
	ptrBad := findMethod(program, "main.T", "PtrBad")
	if ptrBad == nil {
		t.Fatal("no stub for main.T.PtrBad")
	}
	precv, _ := ptrBad["recv"].(map[string]any)
	prty, _ := precv["type"].(map[string]any)
	if prty["kind"] != "pointer" {
		t.Fatalf("pointer-receiver stub recorded receiver %v", prty)
	}
}

// TestQuarantinedMethodUnlowerableSignatureRefuses: the fail-closed edge. If
// the signature itself does not lower there is no honest stub to record, so
// the WHOLE export refuses — never a method set missing an entry, never one
// carrying a guessed signature. `complex128` is a currently-unmodeled type,
// so the parameter is what breaks; the body is unlowerable too.
func TestQuarantinedMethodUnlowerableSignatureRefuses(t *testing.T) {
	const src = `package main

import "fmt"

type U struct{ n int }

func (u U) Bad(c complex128) int { return len(fmt.Sprintf("%v", c)) }

func main() {}
`
	program, err := emitSource(t, src)
	if err == nil {
		t.Fatalf("un-lowerable method SIGNATURE exported anyway: %v", program["methods"])
	}
	if !strings.Contains(err.Error(), "main.U.Bad") {
		t.Fatalf("refusal does not name the method: %v", err)
	}
	if !strings.Contains(err.Error(), "SIGNATURE") {
		t.Fatalf("refusal does not say the signature is the blocker: %v", err)
	}
}
