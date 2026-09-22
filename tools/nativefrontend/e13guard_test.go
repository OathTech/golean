package main

// The E13 option (b) envelope's BOUNDARY after the e13-b RE-AUDIT fix round
// (2026-09-05, findings R1'-1..R1'-4, R2'-1; the first fix round's R1/R2/R7
// history is in the design's §4). The envelope probes every panicky
// non-call operand the emitter can reach: since the re-audit that includes
// the PHASE-1 operands of assignment targets (spec#Assignment_statements — a target's
// index/deref operands are siblings of the RHS's calls; the target's own
// check is the phase-2 store's), address-of operands (`&a[i]` is a
// bounds-checking `index-addr`), array-of-array target bases, the hoisted
// `recover()` residual, and a HOISTED allocating conversion (hoisted when an
// ordered event follows it). The narrowed A6 guard refuses BY NAME only the
// residue — a compound target that contains a call (its address is a
// hoisted temp, its check unprobed) beside a hoisted len/cap/min/max/append/
// copy/make — and the structural-allocation guard refuses a `&T{}`/slice
// literal/allocating conversion whose panicky payload precedes an ordered
// event (gc evaluates such a payload after the call; no probe reaches that
// member), in return-, println- and sink-rooted spellings alike (the census
// descends into a call that ENCLOSES the hoisting construct). Map literals
// and literals forced by an enclosing call lower. Each refusal is a
// per-decl quarantine (the function carries `unsupported`), never a
// whole-export kill.

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

// unseqCount counts the `unseq` statements under the wire function (Stage C:
// a sweep the whole-sweep decision procedure admits — unseq.go `unseqClassify`
// — lowers as ONE `unseq` graph and carries no probe; the legacy path is for
// every other sweep).
func unseqCount(t *testing.T, program map[string]any, name string) int {
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
				if v["stmt"] == "unseq" {
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
func fnine() int { println("f"); return 9 }
func sinkP(p *int, w int) int { return *p + w }
func useT(t *T) int { println("useT"); return t.x }

type T struct{ x int }

// --- phase-1 TARGET operands are probed (R1'-1) ---

func tgtAssertVsLenHoist() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	var iv interface{} = "s"
	x[iv.(int)] = len(b[j]) + wit(5)
	return x[0]
}

func tgtAssertVsMake() int {
	x := make([]int, 1)
	t := []int{1}
	k := 5
	var iv interface{} = "s"
	x[iv.(int)] = len(make([]int, t[k]))
	return x[0]
}

func tgtAssertVsCall() int {
	x := make([]int, 1)
	var iv interface{} = "s"
	x[iv.(int)] = wit(5)
	return x[0]
}

func compoundAssertVsLen() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	var iv interface{} = "s"
	x[iv.(int)] += len(b[j]) + wit(5)
	return x[0]
}

func mapKeyAssertVsLen() int {
	m := map[string]int{}
	b := [][]int{{1}}
	j := 5
	var iv interface{} = 7
	m[iv.(string)] = len(b[j]) + wit(5)
	return m["a"]
}

func mapTgtAssertVsCall() int {
	m := map[string]int{}
	var iv interface{} = 7
	m[iv.(string)] = wit(5)
	return m["a"]
}

// the receive-statement form keeps the target's probe ahead of the statement
func tgtAssertVsRecv() int {
	x := make([]int, 1)
	var iv interface{} = "s"
	ch := make(chan int, 1)
	ch <- 9
	x[iv.(int)] = <-ch
	return x[0]
}

// an array-of-array target's base is probed at its index-addr
func arrayBaseTargetVsLen() int {
	var aa [1][1]int
	i := 5
	b := [][]int{{1}}
	j := 5
	aa[i][0] = len(b[j]) + wit(5)
	return aa[0][0]
}

// --- the min/max guard wiring (R1'-2) ---

func tgtAssertVsMin() int {
	x := make([]int, 1)
	t := []int{1}
	k := 5
	q := 3
	var iv interface{} = "s"
	x[iv.(int)] = min(q, t[k]) + wit(5)
	return x[0]
}

// --- address-of operands are probed as a whole (R1'-1) ---

func addrAssertLeftCall() int {
	a := make([]int, 1)
	var iv interface{} = "s"
	return sinkP(&a[iv.(int)], wit(5))
}

// --- recover(): a hoisted ordered event, its residual probed (R1'-4) ---

func recoverAssertVsLen() (r int) {
	defer func() {
		b := [][]int{{1}}
		j := 5
		r = recover().(int) + len(b[j]) + wit(5)
	}()
	panic(3)
}

// --- allocating conversions hoist when an event follows (R1'-3) ---

func bytesConvVsLen() int {
	s := "ab"
	b := [][]int{{1}}
	j := 5
	return int([]byte(s)[7]) + len(b[j]) + wit(5)
}

func bytesConvSlicePrintroot() {
	s := "ab"
	b := [][]int{{1}}
	j := 5
	println(int([]byte(s)[1:7][0]) + len(b[j]) + wit(5))
}

// no event after: the conversion stays inline, nothing to probe against
func bytesConvNoEvent() int {
	s := "ab"
	return wit(5) + int([]byte(s)[7])
}

// FR-28 transparency: nil-deref-only on both sides stays lowered (the
// raftpb CloneMessage idiom).
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

// --- the narrowed A6 guard's residue: a compound target containing a call ---

func compoundCallTargetVsLen() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	x[fnine()] += len(b[j]) + wit(5)
	return x[0]
}

// --- the structural-allocation class (R2 / R1'-3 / R2'-1) ---

func compositePtrPayload() int {
	s := make([]int, 1)
	i := 9
	return (&T{x: s[i]}).x + wit(5)
}

func compositePtrPayloadPrintroot() {
	s := make([]int, 1)
	i := 9
	println((&T{x: s[i]}).x + wit(5))
}

func sliceLitPayload() int {
	s := make([]int, 1)
	i := 9
	return []int{s[i]}[0] + wit(5)
}

func sliceLitPayloadRecv() int {
	s := make([]int, 1)
	i := 9
	ch := make(chan int, 1)
	ch <- 3
	return []int{s[i]}[0] + <-ch
}

func bytesConvPanickyPayload() int {
	s := "ab"
	i, j := 5, 7
	return int([]byte(s[i:j])[0]) + wit(5)
}

// controls that lower
func compositePtrPayloadNoEvent() int {
	s := make([]int, 1)
	i := 9
	return wit(5) + (&T{x: s[i]}).x
}

func compositeSiblingEvent() int {
	s := make([]int, 1)
	i := 9
	return []int{s[i], wit(7)}[0]
}

func variadicPackThenCall(xs ...int) int { return len(xs) }
func variadicSibling() int {
	s := make([]int, 1)
	i := 9
	return variadicPackThenCall(s[i], wit(7)) + wit(8)
}

func mapLitPayloadVsCall() int {
	s := make([]int, 1)
	i := 9
	return map[int]int{s[i]: 1}[0] + wit(5)
}

func compositePtrInArgThenCall() int {
	s := make([]int, 1)
	i := 9
	return useT(&T{x: s[i]}) + wit(5)
}

// the literal's sibling event INSIDE the same call: not forced, refused
func compositePtrInArgWithSiblingEvent() int {
	s := make([]int, 1)
	i := 9
	return useT2(&T{x: s[i]}, wit(5))
}
func useT2(t *T, w int) int { return t.x + w }

func main() {}
`

func TestPhase1TargetOperandsAreProbed(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	for fn, want := range map[string]int{
		"tgtAssertVsMake":      1, // Stage E E4: make is an E1 participant WITHOUT effect — no effectful event, the sweep stays legacy (probed)
		"arrayBaseTargetVsLen": 1,
		"addrAssertLeftCall":   1,
	} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: a phase-1 target/address-of operand must lower probed, got refusal %q", fn, u)
			continue
		}
		if n := probeCount(t, program, fn); n != want {
			t.Errorf("%s: expected %d unseq-probe(s), got %d", fn, want, n)
		}
	}
	// Stage C (2026-09-19, the whole-sweep migration boundary): the sweeps INSIDE
	// the pilot grammar — a slice-element target or compound target on int
	// slices beside same-package calls / len, with the type assertion as the
	// failing op — lower as ONE `unseq` graph and carry NO probe (v2.1 §3.7:
	// never a mixture). The shapes above stay legacy (a map target, `make`, a
	// receive, an array base, `min`, an address-of operand are outside the pilot).
	// Stage E E2 (2026-09-21): a MAP target whose key is a type assertion (`m[iv.(string)]
	// = wit(5)`, `… = len(b[j]) + wit(5)`) is inside the widened grammar — the map plan on
	// the frozen map value and the asserted key; one graph, no probe.
	// Stage E E3 (2026-09-21): a RECEIVE on the right-hand side (`x[iv.(int)] = <-ch`) is an event
	// occurrence — one graph, no probe.
	// Stage E E4 (2026-09-21): `make` is an E1 participant WITHOUT effect, so `x[iv.(int)] =
	// len(make([]int, t[k]))` has no effectful event and stays on the legacy path (above).
	// Stage E5 E5a (2026-09-22): `min` is an E1 participant (reading (a), RATIFIED [USER]
	// 2026-09-22), so `x[iv.(int)] = min(q, t[k]) + wit(5)` — the target's assertion unordered
	// against t[k] inside min's window and against the later wit — lowers as one graph, no probe.
	for _, fn := range []string{"tgtAssertVsLenHoist", "tgtAssertVsCall", "compoundAssertVsLen",
		"mapKeyAssertVsLen", "mapTgtAssertVsCall", "tgtAssertVsRecv", "tgtAssertVsMin"} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: a pilot-grammar sweep must lower as an unseq graph, got refusal %q", fn, u)
			continue
		}
		if n := unseqCount(t, program, fn); n != 1 {
			t.Errorf("%s: expected exactly one unseq graph (the whole sweep), got %d", fn, n)
		}
		if n := probeCount(t, program, fn); n != 0 {
			t.Errorf("%s: an unseq-lowered sweep must carry no legacy probe (mixture), got %d", fn, n)
		}
	}
}

func TestRecoverResidualAndHoistedConversionAreProbed(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	// recover() is hoisted (`$c := recover()`), so the probed residual sits
	// in the deferred func literal's own wire function; the outer function
	// must simply lower.
	if u := funcRefusal(t, program, "recoverAssertVsLen"); u != "" {
		t.Errorf("recoverAssertVsLen: the hoisted recover()'s residual is probeable, got refusal %q", u)
	}
	// Stage E E4 (2026-09-21): `[]byte(s)` is a pure conversion head in the graph and the checked
	// `[7]` / `[1:7][0]` on the fresh bytes the occurrences beside len and wit — one graph, no probe
	// (the legacy hoist and its residual probe are no longer reached by these sweeps).
	for _, fn := range []string{"bytesConvVsLen", "bytesConvSlicePrintroot", "bytesConvNoEvent"} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: an E4-grammar sweep must lower as an unseq graph, got refusal %q", fn, u)
			continue
		}
		if n := unseqCount(t, program, fn); n != 1 {
			t.Errorf("%s: expected exactly one unseq graph (the whole sweep), got %d", fn, n)
		}
		if n := probeCount(t, program, fn); n != 0 {
			t.Errorf("%s: an unseq-lowered sweep must carry no legacy probe (mixture), got %d", fn, n)
		}
	}
	// Stage C: `iv.(int) + len(b[j]) + wit(5)` is inside the pilot grammar — one
	// `unseq` graph (the assertion, the checked read, len as an E1 event, the
	// call), no probe.
	if u := funcRefusal(t, program, "assertLeftLenHoist"); u != "" {
		t.Errorf("assertLeftLenHoist: a pilot-grammar sweep must lower, got refusal %q", u)
	}
	if n := unseqCount(t, program, "assertLeftLenHoist"); n != 1 {
		t.Errorf("assertLeftLenHoist: expected exactly one unseq graph, got %d", n)
	}
	if n := probeCount(t, program, "assertLeftLenHoist"); n != 0 {
		t.Errorf("assertLeftLenHoist: an unseq-lowered sweep must carry no legacy probe, got %d", n)
	}
	if u := funcRefusal(t, program, "nilOnlyTargetVsMake"); u != "" {
		t.Errorf("nilOnlyTargetVsMake: FR-28's nil-deref transparency must hold, got refusal %q", u)
	}
}

// Stage C (2026-09-19): the narrowed A6 guard's LAST residue — a compound target
// that CONTAINS A CALL beside a hoisted len (`x[fnine()] += len(b[j]) + wit(5)`,
// BUG-102's designed red `compound-call-target-vs-len`) — is inside the pilot
// grammar and lowers as ONE `unseq` graph: the target plan on the call's frozen
// result, the load, `len` as an E1 event, the calls; no probe, no refusal (the
// designed red RETIRES: BUG-102 → the flip is recorded on BUG-104/BUG-112's line).
// The guard's refusal text stays a `lowerdiag` tripwire; nothing in the pilot
// grammar reaches it any more, so this test asserts the graph, not the refusal.
func TestNarrowedA6GuardResidueLowersAsUnseq(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	if u := funcRefusal(t, program, "compoundCallTargetVsLen"); u != "" {
		t.Errorf("compoundCallTargetVsLen: the pilot lowers this sweep as an unseq graph, got refusal %q", u)
	}
	if n := unseqCount(t, program, "compoundCallTargetVsLen"); n != 1 {
		t.Errorf("compoundCallTargetVsLen: expected exactly one unseq graph, got %d", n)
	}
	if n := probeCount(t, program, "compoundCallTargetVsLen"); n != 0 {
		t.Errorf("compoundCallTargetVsLen: an unseq-lowered sweep must carry no legacy probe, got %d", n)
	}
}

func TestStructuralAllocGuard(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	// An allocating conversion whose OWN operand panics stays inline and
	// keeps the operand's probe (both orders of the payload's panic).
	if u := funcRefusal(t, program, "bytesConvPanickyPayload"); u != "" {
		t.Errorf("bytesConvPanickyPayload: an inline conversion with a probed operand must lower, got refusal %q", u)
	}
	if n := probeCount(t, program, "bytesConvPanickyPayload"); n != 1 {
		t.Errorf("bytesConvPanickyPayload: expected the operand's probe to survive (1), got %d", n)
	}
	// Stage E E4 (2026-09-21): the structural-allocation class ENTERS the graph — `&T{…}` and a
	// slice literal are `allocate` bodies (no E1 edge) whose payload reads are the occurrences
	// unordered against the later call / receive: BUG-102's designed reds RETIRE (each sweep ONE
	// `unseq` graph, no probe, no refusal — the guard's refusal text stays a `lowerdiag` tripwire
	// nothing in the grammar reaches). The map literal keeps its legacy probe (E5).
	for _, fn := range []string{"compositePtrPayload", "compositePtrPayloadPrintroot", "sliceLitPayload",
		"sliceLitPayloadRecv", "compositePtrInArgWithSiblingEvent", "compositePtrPayloadNoEvent",
		"compositeSiblingEvent"} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: an E4-grammar sweep must lower as an unseq graph, got refusal %q", fn, u)
			continue
		}
		if n := unseqCount(t, program, fn); n != 1 {
			t.Errorf("%s: expected exactly one unseq graph (the whole sweep), got %d", fn, n)
		}
		if n := probeCount(t, program, fn); n != 0 {
			t.Errorf("%s: an unseq-lowered sweep must carry no legacy probe (mixture), got %d", fn, n)
		}
	}
	// legacy by name, lowering: a variadic pack; a map literal (E5 — one member, gc's, no probe); a
	// literal inside an EARLIER call's argument list (forced before that call, which precedes the
	// later event — the trigger finds nothing observable).
	for _, fn := range []string{"variadicSibling", "mapLitPayloadVsCall", "compositePtrInArgThenCall"} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: must lower (variadic pack / map literal / forced by the enclosing call), got refusal %q", fn, u)
		}
		if n := unseqCount(t, program, fn); n != 0 {
			t.Errorf("%s: expected the legacy path (no unseq graph), got %d graph(s)", fn, n)
		}
	}
	_ = strings.HasPrefix
}
