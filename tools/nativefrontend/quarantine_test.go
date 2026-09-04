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
	// "currently unmodeled"). WHY REFLECTION IS FAR: the frontend
	// lowers a CLOSED WORLD of statically instantiated types, and
	// reflect.TypeOf asks about a value's DYNAMIC type, which the
	// wire's static type channel does not carry — a scope statement
	// about this frontend, not a claim that reflection is unmodelable
	// in principle. No eternal refusal exists: if reflect ever lowers,
	// this test and the corpus siblings go red/green LOUDLY and
	// retarget again.
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
	// Since FR-25 (2026-09-04, lane fr24) a BASIC unlowerable type in the
	// signature is an opaque marker (fr25_test.go); the sigRefusal arm is
	// reached by what no marker covers — an anonymous non-empty struct
	// parameter (FR-13) here.
	const src = `package main

import "fmt"

type U struct{ n int }

func (u U) Bad(s struct{ a int }) int { return len(fmt.Sprintf("%v", s)) }

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

// ---- FR-4: per-declaration quarantine for method STENCILS (lane fr4-rowm,
// 2026-09-04; mono.go quarantinedStencilStub) ----

const quarantineStencilSrc = `package main

import "reflect"

type box[T any] struct{ v T }

// render does not lower (reflect.TypeOf — see quarantineMethodSrc for why
// reflection is the pick): the quarantined STENCIL at box[int].
func (b box[T]) render(prefix string, rest ...int) (string, error) {
	return prefix + reflect.TypeOf(b.v).String(), nil
}

// get lowers: the healthy sibling stencil of the same instantiation.
func (b box[T]) get() T { return b.v }

func (b *box[T]) ptrRender() string { return reflect.TypeOf(b.v).String() }

type renderer interface {
	render(prefix string, rest ...int) (string, error)
	get() int
}

func use() int {
	b := box[int]{v: 3}
	var x any = b
	if r, ok := x.(renderer); ok {
		return r.get()
	}
	return 0
}

func main() { println(use()) }
`

// TestQuarantinedStencilKeepsExport is FR-4's headline: one unlowerable
// method STENCIL used to refuse the WHOLE export (ledger FR-4, the H-3
// residual). The sibling stencil and the rest of the package survive it.
func TestQuarantinedStencilKeepsExport(t *testing.T) {
	program, err := emitSource(t, quarantineStencilSrc)
	if err != nil {
		t.Fatalf("export refused by a quarantinable method stencil: %v", err)
	}
	get := findMethod(program, "main.box[int]", "get")
	if get == nil {
		t.Fatal("the lowerable sibling stencil main.box[int].get is missing from the wire")
	}
	if _, stubbed := get["unsupported"]; stubbed {
		t.Fatal("a lowerable stencil was quarantined")
	}
	if get["body"] == nil {
		t.Fatal("the lowerable sibling stencil lost its body")
	}
	// The instantiated TypeDef itself is on the wire (the stub's receiver
	// needs its declaration).
	if typeDefByName(program, "main.box[int]") == nil {
		t.Fatal("the instantiation's TypeDef main.box[int] is missing")
	}
}

// TestQuarantinedStencilNeverDropped: the stub stays in the instantiation's
// method table under the MANGLED receiver key, carries the REAL
// (substituted) signature — receiver spelling, params, variadic, results —
// and its refusal names the instantiation and the inner cause.
func TestQuarantinedStencilNeverDropped(t *testing.T) {
	program, err := emitSource(t, quarantineStencilSrc)
	if err != nil {
		t.Fatalf("export: %v", err)
	}
	stub := findMethod(program, "main.box[int]", "render")
	if stub == nil {
		t.Fatal("quarantined stencil DROPPED from the method table — interface satisfaction would answer a silently wrong no")
	}
	reason, _ := stub["unsupported"].(string)
	for _, want := range []string{"method main.box[int].render", "FR-4: method stencil at this instantiation does not lower", "reflect", "satisfaction answers, calls fail closed"} {
		if !strings.Contains(reason, want) {
			t.Fatalf("stub reason lacks %q: %q", want, reason)
		}
	}
	if stub["body"] != nil {
		t.Fatal("a quarantined stencil must carry no body")
	}
	params, _ := stub["params"].([]any)
	if len(params) != 2 {
		t.Fatalf("stub params: want 2 (prefix, rest), got %v", stub["params"])
	}
	if v, _ := stub["variadic"].(bool); !v {
		t.Fatal("stub lost the variadic marker (satisfaction compares it)")
	}
	results, _ := stub["results"].([]any)
	if len(results) != 2 {
		t.Fatalf("stub results: want 2 (string, error), got %v", stub["results"])
	}
	recv, _ := stub["recv"].(map[string]any)
	if recv == nil || namedTypeName(recv["type"]) != "main.box[int]" {
		t.Fatalf("stub receiver must be the instantiation's TypeId, got %v", stub["recv"])
	}
	// A POINTER-receiver stencil stubs the same way, receiver spelled as a
	// pointer to the instantiation.
	ptr := findMethod(program, "main.box[int]", "ptrRender")
	if ptr == nil {
		t.Fatal("pointer-receiver stencil dropped")
	}
	if _, stubbed := ptr["unsupported"]; !stubbed {
		t.Fatal("pointer-receiver stencil with an unlowerable body was not quarantined")
	}
	if pr, _ := ptr["recv"].(map[string]any); pr == nil || fmtType(pr["type"]) != "ptr(main.box[int])" {
		t.Fatalf("pointer stub receiver spelling: %v", ptr["recv"])
	}
}

// fmtType renders a wire type as ptr(...)/named for the receiver checks.
func fmtType(t any) string {
	m, _ := t.(map[string]any)
	if m == nil {
		return "?"
	}
	switch m["kind"] {
	case "ptr", "pointer":
		return "ptr(" + fmtType(m["elem"]) + ")"
	case "named":
		return namedTypeName(m)
	}
	return "?"
}

// TestQuarantinedStencilSignatureOpaque: a stencil refused IN ITS SIGNATURE
// (an imported generic instantiation, FR-23 — cedar-go's
// `ImmutableMapSet[EntityUID].All() iter.Seq[EntityUID]`) composes with the
// stencil quarantine: the body emission refuses (FR-23), the stub's
// signature is emitted in SIGNATURE-OPAQUE mode, the marker TypeDef is
// on the wire, and the export survives.
func TestQuarantinedStencilSignatureOpaque(t *testing.T) {
	src := `package main

import "iter"

type set[T comparable] struct{ items []T }

func (s set[T]) size() int { return len(s.items) }

func (s set[T]) All() iter.Seq[T] {
	return func(yield func(T) bool) {
		for _, v := range s.items {
			if !yield(v) {
				return
			}
		}
	}
}

func use() int { return set[int]{items: []int{1, 2}}.size() }

func main() { println(use()) }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused: %v", err)
	}
	size := findMethod(program, "main.set[int]", "size")
	if size == nil || size["body"] == nil {
		t.Fatal("the sibling stencil main.set[int].size did not lower")
	}
	all := findMethod(program, "main.set[int]", "All")
	if all == nil {
		t.Fatal("the FR-23 stencil was dropped from the method table")
	}
	reason, _ := all["unsupported"].(string)
	for _, want := range []string{"method main.set[int].All", "FR-4: method stencil at this instantiation does not lower", "iter.Seq[int]", "FR-23", "opaque marker"} {
		if !strings.Contains(reason, want) {
			t.Fatalf("stub reason lacks %q: %q", want, reason)
		}
	}
	results, _ := all["results"].([]any)
	if len(results) != 1 || namedTypeName(results[0].(map[string]any)["type"]) != "iter.Seq[int]" {
		t.Fatalf("the stub must carry iter.Seq[int] as an opaque named result, got %v", all["results"])
	}
	if typeDefByName(program, "iter.Seq[int]") == nil {
		t.Fatal("the opaque marker TypeDef iter.Seq[int] is missing")
	}
}

// TestQuarantinedStencilRollbackKeepsSharedInstantiation: the SAME
// instantiation registered by a healthy body and by a body that is then
// quarantined (a C6 local-type argument) — the quarantine's mono rollback
// must undo only its own journal entries, so the shared instantiation and
// its stencils stay on the wire and the healthy body keeps its call.
func TestQuarantinedStencilRollbackKeepsSharedInstantiation(t *testing.T) {
	src := `package main

type box[T any] struct{ v T }

func (b box[T]) get() T { return b.v }

func healthy() int { return box[int]{v: 1}.get() }

func local() int {
	type score int
	return int(box[score]{v: 2}.get()) + box[int]{v: 3}.get()
}

func main() { println(healthy() + local()) }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export refused: %v", err)
	}
	if h := funcByName(program, "healthy"); h == nil || h["body"] == nil {
		t.Fatal("healthy did not lower")
	}
	l := funcByName(program, "local")
	if l == nil {
		t.Fatal("local missing")
	}
	if reason, _ := l["unsupported"].(string); !strings.Contains(reason, "function-local defined type score as a type argument") {
		t.Fatalf("local must be quarantined on the C6 naming refusal, got %q", reason)
	}
	if get := findMethod(program, "main.box[int]", "get"); get == nil || get["body"] == nil {
		t.Fatal("the shared instantiation's stencil main.box[int].get was rolled back with the quarantined body")
	}
	if typeDefByName(program, "main.box[int]") == nil {
		t.Fatal("the shared instantiation's TypeDef was rolled back")
	}
	for _, td := range program["types"].([]any) {
		if name, _ := td.(map[string]any)["name"].(string); strings.Contains(name, "score") {
			t.Fatalf("a local-type instantiation leaked onto the wire: %s", name)
		}
	}
}

// fr4-rowm audit fix round A8: anonymousTypeRefusal re-raises BOTH failure
// modes namedTypeName swallows — the C6 key refusal AND enqueueTypeInst's
// (an imported generic instantiation, FR-23) — via instTypeIdForWire, the
// same call namedTypeName made. No emission path reaches the anonymous-type
// text before the type itself refuses (a `unique.Handle[int]` value refuses
// at its declaration), so the helper is pinned directly.
func TestAnonymousTypeRefusalNamesEnqueueCause(t *testing.T) {
	e, pkg := checkSource(t, `package main

import "unique"

var h unique.Handle[int]

func main() { _ = h }
`)
	ty := pkg.Scope().Lookup("h").Type()
	err := e.anonymousTypeRefusal("method", ty)
	if err == nil || !strings.Contains(err.Error(), "FR-23") || !strings.Contains(err.Error(), "unique.Handle[int]") {
		t.Fatalf("an imported generic instantiation must re-raise enqueueTypeInst's FR-23 refusal, got %v", err)
	}
	if strings.Contains(err.Error(), "anonymous type") {
		t.Fatalf("the FR-23 cause must not be hidden behind the anonymous-type text: %v", err)
	}
}
