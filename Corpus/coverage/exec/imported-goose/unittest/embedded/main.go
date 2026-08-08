// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/embedded.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type embedA struct {
	a string
}

type embedB struct {
	embedA
}

type embedC struct {
	*embedB
}

type embedD struct {
	embedC
}

func (a embedA) Foo() string {
	return "embedA.Foo()"
}

func (a embedB) Foo() string {
	return "embedB.Foo()"
}

func (a *embedA) Bar() string {
	return "*embedA.Bar()"
}

func (a *embedB) Car() string {
	return "*embedB.Car()"
}

func returnEmbedVal() embedB {
	return embedB{}
}

func returnEmbedValWithPointer() embedD {
	return embedD{}
}

func useEmbeddedField(d embedD) string {
	x := d.a
	x = d.embedB.a
	d.a = "a1"

	y := &embedD{}
	y.a = "a2"

	return x
}

func useEmbeddedValField() string {
	x := returnEmbedVal().a
	x = returnEmbedValWithPointer().a
	return x
}

func useEmbeddedMethod(d embedD) bool {
	return d.Bar() == d.embedA.Bar()
}

func useEmbeddedMethod2(d embedD) bool {
	d.Car()
	return d.Foo() == d.embedB.Foo()
}

// --- GoLean harness ---
// Authored wrapper.

// Constructed with LIVE embedded pointers: embedD's promotion chain
// goes through embedC's *embedB, so a zero embedD nil-derefs (see the
// latent-panic row below).
func goleanEmbedded() int {
	d := embedD{embedC{&embedB{embedA{a: "z"}}}}
	sum := 0
	if useEmbeddedMethod(d) {
		sum += 10
	}
	if useEmbeddedMethod2(d) {
		sum += 20
	}
	sum += len(returnEmbedVal().a) * 100
	sum += len(d.a)
	return sum
}

// Second latent upstream panic path: useEmbeddedField constructs a
// fresh zero &embedD{} internally and writes through its nil *embedB
// (`y.a = "a2"`), so it panics for ANY argument.
func goleanEmbeddedField() int {
	d := embedD{embedC{&embedB{embedA{a: "z"}}}}
	return len(useEmbeddedField(d))
}

// Latent upstream panic path: returnEmbedValWithPointer() is a zero
// embedD whose promoted .a dereferences the nil *embedB (their
// translation-only tests never execute it).
func goleanEmbeddedValField() int {
	return len(useEmbeddedValField())
}

func main() {}
