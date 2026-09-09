// FR-31 / BUG-098: one receiver promotes distinct private members p.m and q.m.
// The packages deliberately share their package name. Calls must reach both bodies.
package main

import (
	bi "blue/inner"
	ri "red/inner"
)

type Mix struct {
	ri.A
	bi.B
}
type Deep struct{ Mix }
type Alias = Deep
type IfaceMix struct {
	ri.I
	bi.J
}
type PtrMix struct {
	ri.P
	bi.Q
}
type GenericMix struct {
	ri.G[int]
	bi.H[int]
}
type Δ struct{ Mix }

func promotedBodies() (int, int, int, int, int, int) {
	x := Mix{A: 11, B: 22}
	return ri.Read(x), bi.Read(x), ri.Value(x), bi.Value(x), ri.Expr(x), bi.Expr(x)
}
func deepAndAlias() (int, int, bool, bool) {
	x := Alias{DeepMix()}
	return ri.Read(x), bi.Read(x), ri.Is(x), bi.Is(x)
}
func DeepMix() Mix { return Mix{A: 11, B: 22} }
func embeddedInterfaces() (int, int, int, int) {
	x := IfaceMix{I: ri.A(11), J: bi.B(22)}
	return ri.Read(x), bi.Read(x), ri.Value(x), bi.Expr(x)
}
func pointerSets() (bool, bool, bool, bool, int, int) {
	x := PtrMix{P: 11, Q: 22}
	return ri.Is(x), bi.Is(x), ri.Is(&x), bi.Is(&x), ri.Read(&x), bi.Read(&x)
}
func genericBodies() (int, int, int, int) {
	x := GenericMix{G: ri.G[int]{V: 11}, H: bi.H[int]{V: 22}}
	return ri.Read(x), bi.Read(x), ri.Value(x), bi.Expr(x)
}
func unicodeBodies() (int, int, int, int, int, int) {
	x := Δ{Mix{A: 11, B: 22}}
	a, b, c := ri.UnicodeRead(x)
	return a, b, c, bi.UnicodeRead(x), ri.Read(x), bi.Read(x)
}
func concreteValues() (int, int) { return ri.ConcreteValue(11), ri.ConcreteExpr(11) }
func main() {
	println(promotedBodies())
	println(deepAndAlias())
	println(embeddedInterfaces())
	println(pointerSets())
	println(genericBodies())
	println(unicodeBodies())
	println(concreteValues())
	println(constrainedMethods())
}
func constrainedMethods() (int, int, int, int) {
	x := Mix{A: 11, B: 22}
	return ri.GenericRead(x), bi.GenericRead(x), ri.GenericValue(x), bi.GenericValue(x)
}

// Audit R1: both nil promoted-pointer dispatch and the nil value-method
// envelope retain the declaring package when the method spelling collides.
func nilPromotedPointer() int { return ri.Read((*PtrMix)(nil)) }
func nilPrivateValue() int    { return ri.Read((*ri.NilMix)(nil)) }

// Audit R9: gc chooses an exported requirement before any private one,
// including when its spelling sorts after the private name by code point.
type Ordered interface {
	ri.I
	É() int
	Zz() int
}
type OnlyZz int

func (OnlyZz) Zz() int { return 1 }
func missingMethodOrder() int {
	var x any = OnlyZz(0)
	_ = x.(Ordered)
	return 0
}
