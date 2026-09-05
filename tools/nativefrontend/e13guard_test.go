package main

// The narrowed A6 unordered-panic guard and the structural-allocation
// guard (e13-b audit fix round, 2026-09-05, findings R1/R2/R7): the E13
// option (b) envelope probes a panicky non-call operand ONLY where the
// emitter can (`emitExpr`'s hook); wherever it cannot — an assignment/
// IncDec/compound TARGET operand, an address-of operand, an operand
// containing `recover()` or an allocating conversion — a later len/cap/
// make hoist would still realize only the events-first panic order, and
// the guard refuses BY NAME (the first cut deleted the whole A6 family
// and silently pinned those subclasses). A structural allocation (`&T{}`,
// slice/map literal, interface method value) with a panicky payload
// followed by an ordered event is refused too: the allocation evaluates
// its payload at its hoisted position, gc in the residual after the
// call, and no probe can reach gc's member. Each case is a per-decl
// quarantine (the function carries `unsupported`), never a whole-export
// kill; the positive controls pin that the envelope itself is untouched.

import (
	"strings"
	"testing"
)

// funcRefusal returns the `unsupported` text of the wire function name
// ("" when the function lowered).
func funcRefusal(t *testing.T, program map[string]any, name string) string {
	t.Helper()
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		ff, ok := f.(map[string]any)
		if !ok || ff["name"] != name {
			continue
		}
		if u, ok := ff["unsupported"].(string); ok {
			return u
		}
		return ""
	}
	t.Fatalf("function %s not on the wire", name)
	return ""
}

// probeCount counts the `unseq-probe` statements under the wire function.
func probeCount(t *testing.T, program map[string]any, name string) int {
	t.Helper()
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		ff, ok := f.(map[string]any)
		if !ok || ff["name"] != name {
			continue
		}
		n := 0
		var walk func(any)
		walk = func(o any) {
			switch v := o.(type) {
			case map[string]any:
				if v["stmt"] == "unseq-probe" {
					n++
				}
				for _, c := range v {
					walk(c)
				}
			case []any:
				for _, c := range v {
					walk(c)
				}
			}
		}
		walk(ff["body"])
		return n
	}
	t.Fatalf("function %s not on the wire", name)
	return 0
}

const e13GuardSrc = `package main

func wit(x int) int { println("wit", x); return x }

type T struct{ x int }

// R1: assignment TARGET index (a type assertion) vs a hoisted len whose operand panics.
func tgtAssertVsLenHoist() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	var iv interface{} = "s"
	x[iv.(int)] = len(b[j]) + wit(5)
	return x[0]
}

// R1: the same against the unconditional make hoist.
func tgtAssertVsMake() int {
	x := make([]int, 1)
	t := []int{1}
	k := 5
	var iv interface{} = "s"
	x[iv.(int)] = len(make([]int, t[k]))
	return x[0]
}

// R1: compound-assign target.
func compoundAssertVsLen() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	var iv interface{} = "s"
	x[iv.(int)] += len(b[j]) + wit(5)
	return x[0]
}

// R1: map-element TARGET key (D4 consistency — targets are never probed).
func mapKeyAssertVsLen() int {
	m := map[string]int{}
	b := [][]int{{1}}
	j := 5
	var iv interface{} = 7
	m[iv.(string)] = len(b[j]) + wit(5)
	return m["a"]
}

// R1: left material containing recover() is not probed.
func recoverAssertVsLen() (r int) {
	defer func() {
		b := [][]int{{1}}
		j := 5
		r = recover().(int) + len(b[j]) + wit(5)
	}()
	panic(3)
}

// R7: an allocating conversion is not probed either.
func bytesConvVsLen() int {
	s := "ab"
	b := [][]int{{1}}
	j := 5
	return int([]byte(s)[7]) + len(b[j]) + wit(5)
}

// FR-28 transparency: nil-deref-only on both sides stays lowered (the
// raftpb CloneMessage idiom: a pointer-selector TARGET and a len of a
// pointer selector).
func nilOnlyTargetVsMake(x, out *T) {
	type D struct{ data []byte }
	var xd, od *D
	_ = x
	_ = out
	od.data = make([]byte, len(xd.data))
}

// Envelope control: probed left material — lowers with a probe.
func assertLeftLenHoist() int {
	b := [][]int{{1}}
	j := 5
	var iv interface{} = "s"
	return iv.(int) + len(b[j]) + wit(5)
}

// R2: a &composite literal whose payload panics, followed by a call.
func compositePtrPayload() int {
	s := make([]int, 1)
	i := 9
	return (&T{x: s[i]}).x + wit(5)
}

// R2: a slice literal payload, followed by a call.
func sliceLitPayload() int {
	s := make([]int, 1)
	i := 9
	return []int{s[i]}[0] + wit(5)
}

// R2 control: no ordered event after the literal — lowers.
func compositePtrPayloadNoEvent() int {
	s := make([]int, 1)
	i := 9
	return wit(5) + (&T{x: s[i]}).x
}

// R2 control: the event is INSIDE the literal (a sibling element) — lowers
// with the element's probe (the assert-composite-lit row's shape).
func compositeSiblingEvent() int {
	s := make([]int, 1)
	i := 9
	return []int{s[i], wit(7)}[0]
}

// R2 control: a variadic pack is part of the call it feeds — no guard.
func variadicPackThenCall(xs ...int) int { return len(xs) }
func variadicSibling() int {
	s := make([]int, 1)
	i := 9
	return variadicPackThenCall(s[i], wit(7)) + wit(8)
}

func main() {}
`

func TestNarrowedA6GuardRefusesUnprobedLeftMaterial(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	for _, fn := range []string{"tgtAssertVsLenHoist", "compoundAssertVsLen", "mapKeyAssertVsLen", "recoverAssertVsLen", "bytesConvVsLen"} {
		u := funcRefusal(t, program, fn)
		if !strings.Contains(u, "hoisted past UNPROBED panicky material") || !strings.Contains(u, "e13-b audit fix round R1") {
			t.Errorf("%s: expected the narrowed A6 len refusal by name, got %q", fn, u)
		}
	}
	if u := funcRefusal(t, program, "tgtAssertVsMake"); !strings.Contains(u, "make of a potentially-panicking size/hint operand hoisted past UNPROBED") {
		t.Errorf("tgtAssertVsMake: expected the narrowed A6 make refusal by name, got %q", u)
	}
}

func TestNarrowedA6GuardKeepsTheEnvelopeAndTransparency(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	if u := funcRefusal(t, program, "assertLeftLenHoist"); u != "" {
		t.Errorf("assertLeftLenHoist: probed left material must lower, got refusal %q", u)
	}
	if n := probeCount(t, program, "assertLeftLenHoist"); n != 1 {
		t.Errorf("assertLeftLenHoist: expected exactly one unseq-probe, got %d", n)
	}
	if u := funcRefusal(t, program, "nilOnlyTargetVsMake"); u != "" {
		t.Errorf("nilOnlyTargetVsMake: FR-28's nil-deref transparency must hold, got refusal %q", u)
	}
	if n := probeCount(t, program, "bytesConvVsLen"); n != 0 {
		t.Errorf("bytesConvVsLen: an allocating conversion must never be probed, got %d probes", n)
	}
}

func TestStructuralAllocGuard(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	for fn, kind := range map[string]string{"compositePtrPayload": "&composite literal", "sliceLitPayload": "slice literal"} {
		u := funcRefusal(t, program, fn)
		if !strings.HasPrefix(u, "structural allocation ("+kind+") with a potentially-panicking payload") || !strings.Contains(u, "e13-b audit fix round R2") {
			t.Errorf("%s: expected the structural-allocation refusal by name, got %q", fn, u)
		}
	}
	for _, fn := range []string{"compositePtrPayloadNoEvent", "compositeSiblingEvent", "variadicSibling"} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: must lower (no event after the literal / event inside it / a variadic pack), got refusal %q", fn, u)
		}
	}
	if n := probeCount(t, program, "compositeSiblingEvent"); n != 1 {
		t.Errorf("compositeSiblingEvent: expected the element's probe to survive, got %d", n)
	}
}
