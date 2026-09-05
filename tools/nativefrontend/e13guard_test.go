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
		"tgtAssertVsLenHoist": 1, "tgtAssertVsMake": 1, "tgtAssertVsCall": 1,
		"compoundAssertVsLen": 2, "mapKeyAssertVsLen": 1, "mapTgtAssertVsCall": 1,
		"tgtAssertVsRecv": 1, "arrayBaseTargetVsLen": 1, "tgtAssertVsMin": 1,
		"addrAssertLeftCall": 1,
	} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: a phase-1 target/address-of operand must lower probed, got refusal %q", fn, u)
			continue
		}
		if n := probeCount(t, program, fn); n != want {
			t.Errorf("%s: expected %d unseq-probe(s), got %d", fn, want, n)
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
	for _, fn := range []string{"bytesConvVsLen", "bytesConvSlicePrintroot"} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: a hoisted allocating conversion's residual is probeable, got refusal %q", fn, u)
			continue
		}
		if n := probeCount(t, program, fn); n != 1 {
			t.Errorf("%s: expected exactly one unseq-probe over the hoisted conversion's residual, got %d", fn, n)
		}
	}
	if n := probeCount(t, program, "bytesConvNoEvent"); n != 0 {
		t.Errorf("bytesConvNoEvent: an INLINE allocating conversion must never be probed, got %d probes", n)
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
}

func TestNarrowedA6GuardRefusesTheResidue(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	u := funcRefusal(t, program, "compoundCallTargetVsLen")
	if !strings.HasPrefix(u, "len of a potentially-panicking operand hoisted past UNPROBED panicky material") || !strings.Contains(u, "index expression") {
		t.Errorf("compoundCallTargetVsLen: expected the narrowed A6 len refusal naming the unprobed hoisted-address target, got %q", u)
	}
}

func TestStructuralAllocGuard(t *testing.T) {
	program, err := emitSource(t, e13GuardSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	for fn, kind := range map[string]string{
		"compositePtrPayload":               "&composite literal",
		"compositePtrPayloadPrintroot":      "&composite literal",
		"sliceLitPayload":                   "slice literal",
		"sliceLitPayloadRecv":               "slice literal",
		"bytesConvPanickyPayload":           "allocating conversion []byte(string)",
		"compositePtrInArgWithSiblingEvent": "&composite literal",
	} {
		u := funcRefusal(t, program, fn)
		if !strings.HasPrefix(u, "structural allocation ("+kind+") with a potentially-panicking payload") || !strings.Contains(u, "e13-b audit fix round R2") {
			t.Errorf("%s: expected the structural-allocation refusal by name (%s), got %q", fn, kind, u)
		}
	}
	for _, fn := range []string{"compositePtrPayloadNoEvent", "compositeSiblingEvent", "variadicSibling", "mapLitPayloadVsCall", "compositePtrInArgThenCall"} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: must lower (no event after / event inside / variadic pack / map literal / forced by the enclosing call), got refusal %q", fn, u)
		}
	}
	if n := probeCount(t, program, "compositeSiblingEvent"); n != 1 {
		t.Errorf("compositeSiblingEvent: expected the element's probe to survive, got %d", n)
	}
}
