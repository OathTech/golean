package main

// Latitude E13 option (b) (RULED [USER] 2026-09-05, relayed; lane e13-b;
// design docs/2026-09-05_e13-b-design.md): a spec-UNSEQUENCED panicky
// non-call operand (type assertion, slice expression, interface
// comparison, index, dereference, division, shift, slice→array
// conversion) beside a SIBLING ordered event (a call, receive, method
// call, or hoisted built-in) lexically after it. spec#Order_of_evaluation
// orders neither first, so the machine offers BOTH orders through the
// `unseqPanic` pick; the membership rows below certify the two-member
// (sometimes three-member) sets and sample gc, whose realization is
// EARLY for assertions/slices/comparisons and LATE for index/deref/
// division/shift/conversion (docs/evidence/2026-09-05_e13-b/
// gc-realization.txt). The observable is "which panic wins and what ran
// before it": the witness `wit` PRINTS, so the run's output records the
// sibling events that completed before the panic.

var w int

func wit(x int) int { println("wit", x); return x }

func sink(a, b int) int { return a + b }

type T struct{ x int }

func (t *T) M() int { println("M"); return 7 }

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// --- the assertion axis (gc: EARLY — the assertion panics before the sibling event) ---

func assertLeftCall() int {
	var iv interface{} = "s"
	return iv.(int) + wit(5)
}

func assertMiddle() int {
	var iv interface{} = "s"
	return wit(1) + iv.(int) + wit(2)
}

func assertArgSibling() int {
	var iv interface{} = "s"
	return sink(iv.(int), wit(7))
}

func assertCompositeLit() int {
	var iv interface{} = "s"
	return []int{iv.(int), wit(7)}[0]
}

func assertReturnList() int {
	var iv interface{} = "s"
	a, b := func() (int, int) { return iv.(int), wit(7) }()
	return a + b
}

func assertLeftMethod() int {
	var iv interface{} = "s"
	obj := &T{}
	return iv.(int) + obj.M()
}

func assertLeftMakeSlice() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(make([]int, t[k]))
}

func assertLeftLenSliceCall() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(t[k:]) + wit(5)
}

func assertLeftNewCall() int {
	var iv interface{} = "s"
	return iv.(int) + *new(int) + wit(5)
}

func assertLeftAppend() int {
	var iv interface{} = "s"
	s := []int{1}
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(append(s, t[k])) + wit(5)
}

func assertLeftCopy() int {
	var iv interface{} = "s"
	d := []int{1, 2, 3}
	s := []int{9}
	t := []int{1, 2}
	k := 5
	return iv.(int) + copy(d[t[k]:], s)
}

// The sibling call MUTATES the asserted interface: EARLY panics, LATE
// succeeds (the assertion then sees the int) — members differ in STATUS.
func assertVsMutatingCall() int {
	var iv interface{} = "s"
	return iv.(int) + func() int { iv = 4; return 1 }()
}

func sliceLeftCall() int {
	s := []int{1}
	i := 9
	return len(s[i:]) + wit(5)
}

func ifaceCmpLeftCall() int {
	var jv interface{} = []int{1}
	return b2i((jv == jv) == (wit(5) > 0))
}

// --- the index/deref/division/shift/conversion axis (gc: LATE — the sibling event runs first) ---

func indexLeftCall() int {
	s := []int{1}
	i := 9
	return s[i] + wit(5)
}

func indexMiddle() int {
	s := []int{1}
	i := 9
	return wit(1) + s[i] + wit(2)
}

func indexArgSibling() int {
	s := []int{1}
	i := 9
	return sink(s[i], wit(7))
}

func indexCompositeLit() int {
	s := []int{1}
	i := 9
	return []int{s[i], wit(7)}[0]
}

func sendChanIndex() int {
	cs := []chan int{}
	i := 9
	cs[i] <- wit(7)
	return 0
}

func derefLeftCall() int {
	var p *int
	return *p + wit(5)
}

func divLeftCall() int {
	x, z := 7, 0
	return x/z + wit(5)
}

func shiftLeftCall() int {
	x, n := 7, -1
	return x<<n + wit(5)
}

func convLeftCall() int {
	s := []int{1}
	return [2]int(s)[0] + wit(5)
}

// --- two probed operands: the DEFER×RAISE combination realizes the second
// operand's panic ahead of the first's (non-call vs non-call — unordered
// by omission, I-2 UNSEQ), so the set has THREE members ---

func twoIndexLeftCall() int {
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + t[k] + wit(5)
}

func indexAssertLeftCall() int {
	var iv interface{} = "s"
	s := []int{1}
	i := 9
	return s[i] + iv.(int) + wit(5)
}

// --- FORCED positions and residual controls (strict rows) ---

// The call's ARGUMENT panics: the argument is evaluated before the call
// (F2); the left index is unsequenced against the call, so its panic may
// come first (RAISE) or the argument's (DEFER, gc's member) — two members,
// and the argument NEVER waits for the call (no member has `wit 5` printed).
func indexLeftCallArgPanics() int {
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + wit(t[k])
}

func derefLeftIndexArgCall() int {
	var p *int
	t := []int{1, 2}
	k := 5
	return *p + wit(t[k])
}

// Argument only (no sibling operand): FORCED, a singleton — the strict control.
func forcedArgOnly() int {
	t := []int{1, 2}
	k := 5
	return wit(t[k])
}

// The assertion RIGHT of the call: the lexical (events-first) order is the
// only realized member (design §6 residual 1) — a strict row pinning the
// narrowing honestly; gc realizes the same order.
func assertRightCall() int {
	var iv interface{} = "s"
	return wit(5) + iv.(int)
}

// `min` with no later event stays INLINE: both operands evaluate in the
// residual, left to right — the assertion first. A singleton, strict.
func assertLeftMinInline() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + min(t[k], 1)
}

// --- a receive sibling, observed through a witness (the receive itself prints nothing) ---

func assertLeftRecvW() (r int) {
	var iv interface{} = "s"
	ch := make(chan int, 1)
	ch <- 3
	defer func() { recover(); r = len(ch) }()
	return iv.(int) + <-ch
}

func main() {
	println(forcedArgOnly())
}

// --- e13-b audit fix round (2026-09-05): the boundary of the envelope ---
//
// R1 — panicky material the envelope does NOT probe (an assignment/IncDec/
// compound TARGET operand, an address-of operand, an operand containing
// recover() or an allocating conversion) left of a hoisted len/cap/make
// whose operand panics. The first cut deleted the whole A6 guard and these
// lowered as a SILENT single-member answer ≠ gc (gc evaluates the
// assertion first; the machine the hoisted operand's panic). The narrowed
// A6 guard refuses them BY NAME: rows red by design (frontend-export),
// on BUG-102's Cases line (the designed-red entry).

func sinkP(p *int, l, w int) int { return *p + l + w }

// target index assertion vs a hoisted len whose operand panics — gc: the
// interface conversion; a lowering would realize the index panic.
func tgtAssertVsLenHoist() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	var iv interface{} = "s"
	x[iv.(int)] = len(b[j]) + wit(5)
	return x[0]
}

// the same against the unconditional make hoist.
func tgtAssertVsMake() int {
	x := make([]int, 1)
	t := []int{1}
	k := 5
	var iv interface{} = "s"
	x[iv.(int)] = len(make([]int, t[k]))
	return x[0]
}

// compound-assign target.
func compoundAssertVsLen() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	var iv interface{} = "s"
	x[iv.(int)] += len(b[j]) + wit(5)
	return x[0]
}

// map-element TARGET key (design §4 D4: targets are never probed — the
// map-assign path had been left probed; one rule for every target now).
func mapKeyAssertVsLen() int {
	m := map[string]int{}
	b := [][]int{{1}}
	j := 5
	var iv interface{} = 7
	m[iv.(string)] = len(b[j]) + wit(5)
	return m["a"]
}

// left material containing recover() is never probed (purity).
func recoverAssertVsLen() (r int) {
	defer func() {
		b := [][]int{{1}}
		j := 5
		r = recover().(int) + len(b[j]) + wit(5)
	}()
	panic(3)
}

// an address-of operand (`&a[i]` lowers to an inline index-addr, never
// probed) left of the hoisted len.
func addrIndexLeftLenHoist() int {
	a := make([]int, 1)
	i := 9
	b := [][]int{{1}}
	j := 5
	return sinkP(&a[i], len(b[j]), wit(5))
}

// an allocating conversion ([]byte(s)) is never probed (R7: a probe would
// allocate twice).
func bytesConvLeftLenHoist() int {
	s := "ab"
	b := [][]int{{1}}
	j := 5
	return int([]byte(s)[7]) + len(b[j]) + wit(5)
}

// R2 — a STRUCTURAL allocation (a composite-literal `&T{…}`, a slice
// literal) whose payload panics, followed by an ordered event: the
// allocation hoists to its lexical position and evaluates the payload
// there, before the call; gc evaluates it in the residual AFTER the call
// (prints `wit 5`, then panics). Neither order is spec-forced, the
// machine realizes only one, and no probe reaches gc's member. Pre-
// existing on main; refused by name since the audit fix round.

func compositePtrPayloadVsCall() int {
	s := make([]int, 1)
	i := 9
	return (&T{x: s[i]}).x + wit(5)
}

func sliceLitPayloadVsCall() int {
	s := make([]int, 1)
	i := 9
	return []int{s[i]}[0] + wit(5)
}

// The VALUE axis reached through the len shape (E12's known divergence,
// filed as an open BUG at the audit fix round): the assertion SUCCEEDS
// early and FAILS late — gc evaluates `iv.(int)` before the sibling call
// that replaces iv (value 6); the probe evaluates it early too but
// DISCARDS the value, and the residual re-evaluation after the mutating
// call panics. Not statically refusable (whether the early evaluation
// succeeds is a run-time fact) — a red-first row, gc's value pinned.
func assertOkEarlyLenHoist() int {
	var iv interface{} = 3
	b := make([]int, 2)
	j := 0
	return iv.(int) + len(b[j:]) + func() int { iv = "s"; println("mut"); return 1 }()
}
