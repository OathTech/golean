package main

// BUG-095 (docs/BUGS.md): satisfaction of an interface that EMBEDS another
// interface, probed at every dynamic check the machine performs it for
// (type switch, type assertion, comma-ok assertion, nested embedding, a
// type-parameter case instantiated to the embedding interface).
//
// spec#Embedded_interfaces: the method set of J is the UNION of its own
// methods and the embedded interface's; spec#Interface_types: a type
// implements an interface iff its method set is a superset. gc: a type with
// only the embedded interface's method (esOnlyFoo: foo, no bar) does NOT
// implement esJ.
//
// THE TRIGGER, present in every subject: a call / method value / method
// expression / promoted-wrapper dispatch of the EMBEDDED interface's method
// THROUGH the embedding interface (`j.foo()` with j : esJ, foo declared in
// esI). On main the frontend registered esJ's wire declaration from that
// dispatch with the DECLARING interface's (esI's) method set — last writer
// wins — so esJ's requirement list on the wire was {foo} and every check
// below answered "satisfied" for esOnlyFoo.
//
// ORDER-ROBUSTNESS (slice-3 audit): a dispatch of the embedding interface's
// OWN method through it (`j.bar()` with j : esJ) re-registered the FULL set,
// so whether the defect showed depended on emission order. NO such dispatch
// exists in this file — every dispatch through esJ / esK is of a method
// declared in an EMBEDDED interface — so the pins exercise the wrong
// satisfaction directly, whatever order the emitter visits the bodies in.
type esI interface{ foo() int }

type esJ interface {
	esI
	bar() int
}

// esK embeds esJ, which embeds esI: two levels of flattening.
type esK interface {
	esJ
	baz() int
}

// esOnlyFoo implements esI only.
type esOnlyFoo int

func (x esOnlyFoo) foo() int { return int(x) }

// esFooBar implements esJ (and esI), not esK.
type esFooBar int

func (x esFooBar) foo() int { return int(x) }
func (x esFooBar) bar() int { return int(x) * 10 }

// esOnlyBar has esJ's OWN method but lacks the EMBEDDED one: the reverse
// cell — not esI, not esJ.
type esOnlyBar int

func (x esOnlyBar) bar() int { return int(x) }

// esAll implements esK.
type esAll int

func (x esAll) foo() int { return int(x) }
func (x esAll) bar() int { return int(x) * 10 }
func (x esAll) baz() int { return int(x) * 100 }

// esThroughJ is the trigger: esI's method dispatched through esJ.
func esThroughJ(j esJ) int { return j.foo() }

// esThroughK dispatches the method declared TWO levels down (esI's foo)
// through esK — the two-level poisoner (esK's own baz is never dispatched
// through esK in this file; see ORDER-ROBUSTNESS above).
func esThroughK(k esK) int { return k.foo() }

// esClassify reports the FIRST matching case, most specific first.
func esClassify(i esI) int {
	switch i.(type) {
	case esK:
		return 3
	case esJ:
		return 2
	case esI:
		return 1
	default:
		return 0
	}
}

func esClassifyAny(x any) int {
	switch x.(type) {
	case esK:
		return 3
	case esJ:
		return 2
	case esI:
		return 1
	default:
		return 0
	}
}

// embeddingSatisfactionTypeSwitch: gc 1 2 3 0 2.
func embeddingSatisfactionTypeSwitch() (int, int, int, int, int) {
	trigger := esThroughJ(esFooBar(1)) + esThroughK(esAll(1))
	return esClassify(esOnlyFoo(5)), esClassify(esFooBar(6)), esClassify(esAll(7)),
		esClassifyAny(esOnlyBar(8)), trigger
}

// embeddingSatisfactionAssert: the one-value assertion — gc panics
// (esOnlyFoo lacks esJ's own bar); the asserted value then dispatches only
// the embedded method, so the file stays free of own-method dispatch.
func embeddingSatisfactionAssert() int {
	trigger := esThroughJ(esFooBar(1))
	var i esI = esOnlyFoo(7)
	j := i.(esJ)
	return j.foo() + trigger
}

// embeddingSatisfactionAssertOk: comma-ok against esJ for each dynamic
// type — gc false true true false, plus the trigger value 1.
func embeddingSatisfactionAssertOk() (bool, bool, bool, bool, int) {
	trigger := esThroughJ(esFooBar(1))
	var a esI = esOnlyFoo(1)
	var b esI = esFooBar(2)
	var c esI = esAll(3)
	var d any = esOnlyBar(4)
	_, okA := a.(esJ)
	_, okB := b.(esJ)
	_, okC := c.(esJ)
	_, okD := d.(esJ)
	return okA, okB, okC, okD, trigger
}

// embeddingSatisfactionNested: esK's flattened set {foo, bar, baz} —
// esFooBar (two of three) does not implement esK, esOnlyFoo (one of three)
// does not either; esAll does; the asserted esK value dispatches the
// two-levels-down foo (the poisoner). gc false false true 1 3.
func embeddingSatisfactionNested() (bool, bool, bool, int, int) {
	var a esI = esFooBar(2)
	var c esI = esOnlyFoo(4)
	var b esI = esAll(1)
	_, okA := a.(esK)
	_, okC := c.(esK)
	k, okB := b.(esK)
	sum := 0
	if okB {
		sum = k.foo()
	}
	return okA, okC, okB, sum, esClassify(esAll(9))
}

// embeddingSatisfactionNegative: the reverse cell — esOnlyBar has esJ's
// OWN method but not the EMBEDDED one; gc names the first unmet method
// in name order: `missing method foo`.
func embeddingSatisfactionNegative() int {
	trigger := esThroughJ(esFooBar(1))
	var x any = esOnlyBar(3)
	j := x.(esJ)
	return j.foo() + trigger
}

// embeddingSatisfactionMethodValue: the trigger as a METHOD VALUE
// (`j.foo` bound, then called). gc 1 false true.
func embeddingSatisfactionMethodValue() (int, bool, bool) {
	var j esJ = esFooBar(1)
	f := j.foo
	var a esI = esOnlyFoo(2)
	var b esI = esFooBar(3)
	_, okA := a.(esJ)
	_, okB := b.(esJ)
	return f(), okA, okB
}

// embeddingSatisfactionMethodExpr: the trigger as a METHOD EXPRESSION
// (`esJ.foo`). gc 1 false true.
func embeddingSatisfactionMethodExpr() (int, bool, bool) {
	var j esJ = esFooBar(1)
	g := esJ.foo
	var a esI = esOnlyFoo(2)
	var b esI = esFooBar(3)
	_, okA := a.(esJ)
	_, okB := b.(esJ)
	return g(j), okA, okB
}

// esBox embeds an esJ FIELD: its promoted foo forwards through the field's
// interface (the promotion-wrapper dispatch shape). gc 1 false true.
type esBox struct{ esJ }

func embeddingSatisfactionPromoted() (int, bool, bool) {
	b := esBox{esFooBar(1)}
	var a esI = esOnlyFoo(2)
	var c esI = esFooBar(3)
	_, okA := a.(esJ)
	_, okC := c.(esJ)
	return b.foo(), okA, okC
}

// embeddingSatisfactionMethodExprPromoted: the trigger as a METHOD
// EXPRESSION over the EMBEDDING STRUCT (`esBox.foo` — foo declared in esI,
// reached through esBox's embedded esJ field): the func value takes an
// esBox and is its promotion wrapper. Before the bug095-096 audit fix R4
// the frontend quarantined this shape (`main.esBox: static type is not a
// value interface`). gc 1 false true.
func embeddingSatisfactionMethodExprPromoted() (int, bool, bool) {
	g := esBox.foo
	var a esI = esOnlyFoo(2)
	var c esI = esFooBar(3)
	_, okA := a.(esJ)
	_, okC := c.(esJ)
	return g(esBox{esFooBar(1)}), okA, okC
}

// esWhich is $GOROOT/test/typeparam/typeswitch3.go's shape: `case T` with
// T instantiated to the embedding interface, the bound value's method
// called in the arm (the trigger inside the generic body).
func esWhich[T esI](i esI) int {
	switch x := i.(type) {
	case T:
		return 100 + x.foo()
	case esOnlyFoo:
		return 200 + x.foo()
	default:
		return 300 + x.foo()
	}
}

// embeddingSatisfactionGeneric: gc 211 112 110 205.
func embeddingSatisfactionGeneric() (int, int, int, int) {
	return esWhich[esJ](esOnlyFoo(11)), esWhich[esJ](esFooBar(12)),
		esWhich[esI](esOnlyFoo(10)), esWhich[esFooBar](esOnlyFoo(5))
}

func main() {
	embeddingSatisfactionTypeSwitch()
	embeddingSatisfactionAssertOk()
	embeddingSatisfactionNested()
	embeddingSatisfactionMethodValue()
	embeddingSatisfactionMethodExpr()
	embeddingSatisfactionPromoted()
	embeddingSatisfactionMethodExprPromoted()
	embeddingSatisfactionGeneric()
}
