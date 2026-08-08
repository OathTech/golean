// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/struct_pointers.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type TwoInts struct {
	x uint64
	y uint64
}

type S struct {
	a uint64
	b TwoInts
	c bool
}

func NewS() *S {
	return &S{
		a: 2,
		b: TwoInts{x: 1, y: 2},
		c: true,
	}
}

func (s *S) readA() uint64 {
	return s.a
}

func (s *S) readB() TwoInts {
	return s.b
}

func (s S) readBVal() TwoInts {
	return s.b
}

func (s *S) writeB(two TwoInts) {
	s.b = two
}

func (s *S) negateC() {
	s.c = !s.c
}

func (s *S) refC() *bool {
	return &s.c
}

func localSRef() *TwoInts {
	// this is all modeled correctly because if local variables escape Go
	// allocates them on the heap; we model stack variables linearly but can
	// optionally switch to a heavier-weight but more flexible heap-based model
	var s S
	return &s.b
}

func setField() S {
	var s S
	s.a = 0
	s.c = true
	return s
}

// --- GoLean harness ---
// Authored wrapper.

// BUG-048 note: `s.readBVal()` (value receiver via the pointer var s)
// is the wrong-stuck class pinned by
// methods/value-receiver-via-pointer-var — the wrapper calls it on the
// DEREFERENCED value instead and leaves the class to its pin.
func goleanStructPointers() int {
	s := NewS()
	sum := int(s.readA())
	sum += int(s.readB().x) * 10
	v := *s
	sum += int(v.readBVal().y) * 100
	s.writeB(TwoInts{x: 5, y: 6})
	sum += int(s.readB().y) * 1000
	s.negateC()
	if *s.refC() {
		sum += 10000
	} else {
		sum += 20000
	}
	sum += int(localSRef().x)
	x := setField()
	if x.c {
		sum += 100000
	}
	return sum
}

func main() {}
