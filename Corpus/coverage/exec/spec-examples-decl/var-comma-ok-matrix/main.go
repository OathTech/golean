package main

// BUG-057 edge enumeration (bug-fix arc slice 2, 2026-08-19).
//
// spec#Variable_declarations gives the two-variable comma-ok VAR
// DECLARATION for all three comma-ok sources: a receive operator
// (spec#Receive_operator), a map index (spec#Index_expressions) and a type
// assertion (spec#Type_assertions). The declaration comes in an untyped
// form (`var v, ok = x`) and a typed form (`var v, ok T = x`) — where T
// types BOTH names, so T is either bool (and then the value is a bool
// too) or an INTERFACE type both values are assignable to, the shape
// spec#Type_assertions itself writes as `var v, ok interface{} = x.(T)`;
// either name may be the blank identifier; and the declaration may sit at
// function scope or at package scope.
//
// THE MASKING LESSON (P3 audit, BUG-057's MASKING record): a comma-ok case
// whose ok is FALSE cannot distinguish "the machine delivered ok" from
// "the machine dropped ok", because the dropped flag's zero value IS
// false. Every subject below therefore observes a TRUE ok.
//
// F-10 (the typed-form limitation the P3 delta-review recorded): the old
// typed-form subject returned `x && ok`, one bit, so it could not tell a
// dropped VALUE from a dropped OK. Every subject here returns the value
// and the ok as SEPARATE observables, so the two deliveries are two
// distinct observations: correct is (value, true); a dropped ok is
// (value, false); a dropped value is (zero, true).

// ---- supporting declarations ----

func seedInt(v int) chan int {
	c := make(chan int, 1)
	c <- v
	return c
}

func seedBool(v bool) chan bool {
	c := make(chan bool, 1)
	c <- v
	return c
}

func two() (int, int) { return 4, 5 }

// ---- function-local: receive ----

// recvUntyped: `var v, ok = <-ch` on a LIVE channel. go: 7, true.
func recvUntyped() (int, bool) {
	ch := seedInt(7)
	var v, ok = <-ch
	return v, ok
}

// recvUntypedBlankValue: `var _, ok = <-ch`. go: true.
func recvUntypedBlankValue() bool {
	ch := seedInt(7)
	var _, ok = <-ch
	return ok
}

// recvUntypedBlankOk: `var v, _ = <-ch` — the value-delivery half alone.
// go: 7.
func recvUntypedBlankOk() int {
	ch := seedInt(7)
	var v, _ = <-ch
	return v
}

// recvTyped: the spec's `var x, ok T = <-ch` with T = bool, on a live
// channel carrying TRUE — so the value and the ok are independently
// observable (F-10). go: true, true.
func recvTyped() (bool, bool) {
	ch := seedBool(true)
	var v, ok bool = <-ch
	return v, ok
}

// recvTypedBlankValue: `var _, ok bool = <-ch`. go: true.
func recvTypedBlankValue() bool {
	ch := seedBool(true)
	var _, ok bool = <-ch
	return ok
}

// recvTypedBlankOk: `var v, _ bool = <-ch`. go: true.
func recvTypedBlankOk() bool {
	ch := seedBool(true)
	var v, _ bool = <-ch
	return v
}

// ---- function-local: map index ----

// indexUntyped: `var v, ok = m[k]` on a PRESENT key. go: 7, true.
func indexUntyped() (int, bool) {
	m := map[string]int{"k": 7}
	var v, ok = m["k"]
	return v, ok
}

func indexUntypedBlankValue() bool {
	m := map[string]int{"k": 7}
	var _, ok = m["k"]
	return ok
}

func indexUntypedBlankOk() int {
	m := map[string]int{"k": 7}
	var v, _ = m["k"]
	return v
}

// indexTyped: `var v, ok bool = m[k]` — present key whose VALUE is true,
// so value and ok are independently observable. go: true, true.
func indexTyped() (bool, bool) {
	m := map[string]bool{"k": true}
	var v, ok bool = m["k"]
	return v, ok
}

func indexTypedBlankValue() bool {
	m := map[string]bool{"k": true}
	var _, ok bool = m["k"]
	return ok
}

func indexTypedBlankOk() bool {
	m := map[string]bool{"k": true}
	var v, _ bool = m["k"]
	return v
}

// ---- function-local: type assertion ----

// assertUntyped: `var v, ok = x.(T)` with a SUCCEEDING assertion.
// go: 7, true.
func assertUntyped() (int, bool) {
	var x any = 7
	var v, ok = x.(int)
	return v, ok
}

func assertUntypedBlankValue() bool {
	var x any = 7
	var _, ok = x.(int)
	return ok
}

func assertUntypedBlankOk() int {
	var x any = 7
	var v, _ = x.(int)
	return v
}

// assertTyped: `var v, ok bool = x.(bool)` on a boxed TRUE. go: true, true.
func assertTyped() (bool, bool) {
	var x any = true
	var v, ok bool = x.(bool)
	return v, ok
}

func assertTypedBlankValue() bool {
	var x any = true
	var _, ok bool = x.(bool)
	return ok
}

func assertTypedBlankOk() bool {
	var x any = true
	var v, _ bool = x.(bool)
	return v
}

// ---- the INTERFACE-typed form of the typed declaration ----
//
// `var v, ok interface{} = x.(T)` is the shape spec#Type_assertions
// writes; the same T-types-both-names rule admits it for the receive and
// index sources too. Both values are BOXED into interface cells, which is
// the implicit multi-value interface conversion the interfaces campaign
// has deferred — so all three refuse at the frontend boundary today. They
// are pinned here because the BUG-057 fix reroutes exactly these specs:
// the refusal must survive the reroute rather than become a silent
// unboxed store. go (were they supported): 7, true.

func recvTypedIface() (any, any) {
	ch := seedInt(7)
	var v, ok interface{} = <-ch
	return v, ok
}

func indexTypedIface() (any, any) {
	m := map[string]int{"k": 7}
	var v, ok interface{} = m["k"]
	return v, ok
}

func assertTypedIface() (any, any) {
	var x any = 7
	var v, ok interface{} = x.(int)
	return v, ok
}

// ---- package-level (the $pkginit path, correct-by-construction per the
// BUG-057 entry — pinned here so the fix cannot silently disturb it) ----

var pChRU = seedInt(7)
var pChRUBV = seedInt(7)
var pChRUBO = seedInt(7)
var pChRT = seedBool(true)
var pChRTBV = seedBool(true)
var pChRTBO = seedBool(true)

var pvRU, pokRU = <-pChRU
var _, pokRUBV = <-pChRUBV
var pvRUBO, _ = <-pChRUBO

var pvRT, pokRT bool = <-pChRT
var _, pokRTBV bool = <-pChRTBV
var pvRTBO, _ bool = <-pChRTBO

var pMI = map[string]int{"k": 7}
var pMB = map[string]bool{"k": true}

var pvIU, pokIU = pMI["k"]
var _, pokIUBV = pMI["k"]
var pvIUBO, _ = pMI["k"]

var pvIT, pokIT bool = pMB["k"]
var _, pokITBV bool = pMB["k"]
var pvITBO, _ bool = pMB["k"]

var pAI any = 7
var pAB any = true

var pvAU, pokAU = pAI.(int)
var _, pokAUBV = pAI.(int)
var pvAUBO, _ = pAI.(int)

var pvAT, pokAT bool = pAB.(bool)
var _, pokATBV bool = pAB.(bool)
var pvATBO, _ bool = pAB.(bool)

func pkgRecvUntyped() (int, bool)      { return pvRU, pokRU }
func pkgRecvUntypedBlankValue() bool   { return pokRUBV }
func pkgRecvUntypedBlankOk() int       { return pvRUBO }
func pkgRecvTyped() (bool, bool)       { return pvRT, pokRT }
func pkgRecvTypedBlankValue() bool     { return pokRTBV }
func pkgRecvTypedBlankOk() bool        { return pvRTBO }
func pkgIndexUntyped() (int, bool)     { return pvIU, pokIU }
func pkgIndexUntypedBlankValue() bool  { return pokIUBV }
func pkgIndexUntypedBlankOk() int      { return pvIUBO }
func pkgIndexTyped() (bool, bool)      { return pvIT, pokIT }
func pkgIndexTypedBlankValue() bool    { return pokITBV }
func pkgIndexTypedBlankOk() bool       { return pvITBO }
func pkgAssertUntyped() (int, bool)    { return pvAU, pokAU }
func pkgAssertUntypedBlankValue() bool { return pokAUBV }
func pkgAssertUntypedBlankOk() int     { return pvAUBO }
func pkgAssertTyped() (bool, bool)     { return pvAT, pokAT }
func pkgAssertTypedBlankValue() bool   { return pokATBV }
func pkgAssertTypedBlankOk() bool      { return pvATBO }

// ---- positions the declaration can occupy ----

// commaOkInFuncLit: the declaration inside a function literal, which is a
// separate emitter body. go: 7, true.
func commaOkInFuncLit() (int, bool) {
	m := map[string]int{"k": 7}
	f := func() (int, bool) {
		var v, ok = m["k"]
		return v, ok
	}
	return f()
}

// commaOkGroupedSpec: a GROUPED var declaration whose specs mix an
// ordinary initializer with a comma-ok one — the multi-spec shape the
// single-spec fix must not drop; the comma-ok spec sits BETWEEN two
// ordinary ones so a reordering would show. go: 2, 7, true.
func commaOkGroupedSpec() (int, int, bool) {
	m := map[string]int{"k": 7}
	var (
		n       = 1
		v, ok   = m["k"]
		trailer = 2
	)
	return n * trailer, v, ok
}

// commaOkIfaceValue: a map with INTERFACE element type — the comma-ok
// value needs no boxing (the component is already an interface), so this
// must not hit the multi-value interface-conversion refusal. go: 7, true.
func commaOkIfaceValue() (int, bool) {
	m := map[string]any{"k": 7}
	var v, ok = m["k"]
	n, isInt := v.(int)
	return n, ok && isInt
}

// commaOkShadowCapture: spec#Declarations_and_scope — "the scope of a
// variable identifier declared inside a function begins at the end of the
// VarSpec", so the `v` INSIDE the initializer is the OUTER v (== 1), not
// the one being declared. go: 7, true.
func commaOkShadowCapture() (int, bool) {
	m := map[int]int{1: 7}
	v := 1
	{
		var v, ok = m[v]
		return v, ok
	}
}

// commaOkAfterGoto: the declaration at the TOP LEVEL of a goto-restructured
// function body, where degradeGotoDeclares rewrites source declarations
// into assignments to pre-hoisted cells. go: 7, true.
func commaOkAfterGoto() (int, bool) {
	m := map[string]int{"k": 7}
	n := 0
again:
	var v, ok = m["k"]
	n++
	if n < 2 {
		goto again
	}
	return v, ok
}

// ---- the adjacent tuple-call declaration (NOT comma-ok) ----
//
// `var a, b = two()` pairs two names with one MULTI-VALUE CALL. The
// BUG-057 entry records this shape as FAILING CLOSED function-locally
// while the comma-ok shapes silently mis-lower; these two rows pin the
// classification explicitly so the arity fix cannot flip it to a new
// silent mis-lower without the baseline saying so.

// tupleCallUntyped: `var a, b = two()`. go: 4, 5.
func tupleCallUntyped() (int, int) {
	var a, b = two()
	return a, b
}

// tupleCallTyped: `var a, b int = two()`. go: 4, 5.
func tupleCallTyped() (int, int) {
	var a, b int = two()
	return a, b
}
