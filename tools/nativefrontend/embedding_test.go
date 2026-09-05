package main

import (
	"encoding/json"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

// embeddingSrc dispatches the EMBEDDED interface's method (foo, declared in
// I) through the EMBEDDING interface J in every shape the emitter registers
// an interface from at a dispatch site: a call, a method value, a method
// expression, and a promotion wrapper over an embedded J field.
const embeddingSrc = `package main

type I interface{ foo() int }
type J interface {
	I
	bar()
}
type myint int

func (x myint) foo() int { return int(x) }

func through(j J) int   { return j.foo() }
func viaValue(j J) int  { f := j.foo; return f() }
func viaExpr(j J) int   { return J.foo(j) }
type box struct{ J }
func viaPromoted(b box) int { return b.foo() }

func main() {
	var i I = myint(1)
	_, _ = i.(J)
}
`

// TestEmbeddingInterfaceDefKeepsOwnMethods — BUG-095 guard (RED-FIRST on
// main's emitter: J's `interface` TypeDef carried only {foo}). The
// dispatch sites registered the method's DECLARING interface (I) under
// the STATIC operand's name (J); noteInterface was last-writer-wins, so
// J's requirement list on the wire shrank to I's and the machine answered
// `x.(J)` / `case J` "satisfied" for a type lacking J's own bar.
func TestEmbeddingInterfaceDefKeepsOwnMethods(t *testing.T) {
	program, err := emitSource(t, embeddingSrc)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	found := false
	for _, td := range program["types"].([]any) {
		m := td.(map[string]any)
		if m["name"] != "main.J" {
			continue
		}
		found = true
		def := m["def"].(map[string]any)
		if def["kind"] != "interface" {
			t.Fatalf("main.J def kind = %v, want interface", def["kind"])
		}
		names := []string{}
		for _, sig := range def["methods"].([]any) {
			names = append(names, sig.(map[string]any)["name"].(string))
		}
		if got := strings.Join(names, ","); got != "bar,foo" {
			t.Fatalf("main.J wire method set = [%s], want [bar,foo] (embedded foo + own bar)", got)
		}
	}
	if !found {
		t.Fatalf("no main.J interface TypeDef on the wire")
	}
}

// TestNoteInterfaceConflictRecorded — the fail-closed half: registering
// one wire name with two NON-IDENTICAL method sets is recorded, and
// emitProgram refuses the export on it (the mechanism that let BUG-095
// pass silently is now a named refusal).
func TestNoteInterfaceConflictRecorded(t *testing.T) {
	mk := func(names ...string) *types.Interface {
		fns := []*types.Func{}
		for _, n := range names {
			sig := types.NewSignatureType(nil, nil, nil, nil, nil, false)
			fns = append(fns, types.NewFunc(token.NoPos, nil, n, sig))
		}
		return types.NewInterfaceType(fns, nil).Complete()
	}
	e := &emitter{}
	e.noteInterface("main.X", mk("foo"))
	e.noteInterface("main.X", mk("foo")) // identical: no conflict
	if len(e.ifaceConflicts) != 0 {
		t.Fatalf("identical re-registration recorded a conflict: %v", e.ifaceConflicts)
	}
	e.noteInterface("main.X", mk("bar", "foo"))
	if len(e.ifaceConflicts) != 1 || !strings.HasPrefix(e.ifaceConflicts[0], "main.X") {
		t.Fatalf("non-identical re-registration not recorded: %v", e.ifaceConflicts)
	}
	if e.seenInterfaces["main.X"].NumMethods() != 1 {
		t.Fatalf("a conflicting registration must not overwrite the first")
	}
}

// promotedMethodExprSrc: a METHOD EXPRESSION over a STRUCT whose method is
// promoted from an EMBEDDED INTERFACE field (`S.foo`, `type S struct{ J }`).
const promotedMethodExprSrc = `package main

type I interface{ foo() int }
type J interface {
	I
	bar()
}
type myint int

func (x myint) foo() int { return int(x) }
func (x myint) bar()     {}

type S struct{ J }

func viaExpr() int { f := S.foo; return f(S{myint(7)}) }

func main() { println(viaExpr()) }
`

// TestPromotedMethodExpressionLowers — audit fix R4 (bug095-096,
// 2026-09-05): the method-expression arm took its INTERFACE branch on the
// method's DECLARING receiver alone, so `S.foo` (operand a struct, method
// declared in the embedded interface I) was quarantined as `main.S: static
// type is not a value interface`. The func value is S's promotion wrapper
// `main.S.foo`; the body must lower with no `unsupported` marker.
func TestPromotedMethodExpressionLowers(t *testing.T) {
	program, err := emitSource(t, promotedMethodExprSrc)
	if err != nil {
		t.Fatalf("emit: %v", err)
	}
	found := false
	for _, f := range program["funcs"].([]any) {
		m := f.(map[string]any)
		if m["name"] != "viaExpr" {
			continue
		}
		found = true
		if reason, quarantined := m["unsupported"]; quarantined {
			t.Fatalf("viaExpr quarantined: %v", reason)
		}
		if !strings.Contains(fmtJSON(m["body"]), `"main.S.foo"`) {
			t.Fatalf("viaExpr body does not reference the promotion wrapper main.S.foo: %s", fmtJSON(m["body"]))
		}
	}
	if !found {
		t.Fatalf("no viaExpr func on the wire")
	}
}

func fmtJSON(v any) string {
	b, _ := json.Marshal(v)
	return string(b)
}
