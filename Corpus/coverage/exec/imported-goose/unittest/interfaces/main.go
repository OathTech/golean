// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/interfaces.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type Fooer interface {
	Foo()
}

type concreteFooer struct {
	a uint64
}

type FooerUser struct {
	f Fooer
}

func (f *concreteFooer) Foo() {
}

func fooConsumer(f Fooer) {
	f.Foo()
}

func testAssignConcreteToInterface(x *Fooer) {
	c := &concreteFooer{}
	*x = c
}

func testPassConcreteToInterfaceArg() {
	c := &concreteFooer{}
	fooConsumer(c)

	var f Fooer = c
	fooConsumer(f)
	c.Foo()
	f.Foo()
}

func testPassConcreteToInterfaceArgSpecial() ([]Fooer, map[uint64]Fooer, FooerUser) {
	c1 := &concreteFooer{}
	c2 := &concreteFooer{}

	l := []Fooer{c1, c2}

	m := make(map[uint64]Fooer)
	m[10] = c1

	f := FooerUser{c1}

	return l, m, f
}

func takesVarArgsInterface(fs ...Fooer) {
	fs[0].Foo()
}

func test() {
	takesVarArgsInterface(&concreteFooer{}, &concreteFooer{})
}

func returnConcrete() (*concreteFooer, uint64) {
	return &concreteFooer{}, 10
}

// converts an object into an interface in a multiple return destructuring statement.
func testMultiReturn(x *Fooer) uint64 {
	var y uint64
	*x, y = returnConcrete()
	return y
}

func testReturnStatment() Fooer {
	var y *concreteFooer = &concreteFooer{}
	return y
}

func testConversionInEq(f Fooer) bool {
	c := &concreteFooer{}
	f = c

	return c == f
}

func takeMultiple(a uint64, f ...Fooer) {
}

func giveMultiple() (uint64, Fooer, *concreteFooer) {
	return 0, &concreteFooer{}, &concreteFooer{}
}

func testConversionInMultipleReturnPassThrough() (uint64, Fooer, Fooer) {
	return giveMultiple()
}

// See "special case" in https://go.dev/ref/spec#Calls
func testConversionInMultiplePassThrough() {
	takeMultiple(giveMultiple())
}

type PointerInterface interface {
	Foo()
	B()
}

type concrete1 struct {
}

func (c concrete1) Foo() {
}

func (c *concrete1) B() {
}

func testPtrMset() {
	a := &concrete1{}
	var p PointerInterface = a
	var f Fooer = *a
	p.B()
	f.Foo()
}

func pointerAny() *any {
	return new(any)
}

// --- GoLean harness ---
// Authored wrapper.

func goleanInterfaces() int {
	var f Fooer
	testAssignConcreteToInterface(&f)
	sum := 0
	if f != nil {
		sum++
	}
	testPassConcreteToInterfaceArg()
	l, m, fu := testPassConcreteToInterfaceArgSpecial()
	sum += len(l)*10 + len(m)*100
	if fu.f != nil {
		sum += 1000
	}
	test()
	sum += int(testMultiReturn(&f)) * 10000
	if testReturnStatment() != nil {
		sum += 100000
	}
	if testConversionInEq(&concreteFooer{}) {
		sum += 200000
	}
	a, g1, g2 := testConversionInMultipleReturnPassThrough()
	sum += int(a)
	if g1 != nil && g2 != nil {
		sum += 400000
	}
	testConversionInMultiplePassThrough()
	testPtrMset()
	if pointerAny() != nil {
		sum += 800000
	}
	return sum
}

func main() {}
