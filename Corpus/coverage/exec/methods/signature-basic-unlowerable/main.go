// FR-25 (2026-09-04, lane fr24; the [USER]-approved rider «(3) yes, makes
// sense», relayed by the coordinator): an unlowerable BASIC type in a
// method/func SIGNATURE or an interface REQUIREMENT list — complex128 here,
// FR-15's kind — is an opaque `named complex128` marker with an existence-
// only `unsupported` TypeDef (FR-23's signature-opaque mode, widened), so
// the DECLARATION lowers, satisfaction answers exactly (the requirement
// list stays complete), and only a VALUE of the type or a CALL reaching
// the declaration refuses by name. Before FR-25 the interface below or the
// method `Bad` killed the WHOLE export ("basic type complex128" — the
// sigRefusal arm); this is the shape behind cedar-go's `reflect.Type`
// (`OverflowComplex(complex128)`, reached from encoding/binary.sizeof).
// Legal Go; gc PASS on every subject.
package main

type Kinder interface {
	Kind() int
	OverflowComplex(x complex128) bool
}

type Yes struct{ k int }

func (y Yes) Kind() int                       { return y.k }
func (y Yes) OverflowComplex(x complex128) bool { return real(x) > float64(y.k) }

type No struct{}

func (No) Kind() int { return 2 }

// ifaceUncalled: the interface with the complex128 requirement is
// DECLARED and used for satisfaction only — Yes satisfies, No does not.
func ifaceUncalled() int {
	vals := []any{Yes{k: 1}, No{}}
	out := 0
	for i, v := range vals {
		if k, ok := v.(Kinder); ok {
			out += (i + 1) * 10 * k.Kind()
		} else {
			out += i + 1
		}
	}
	return out
}

// ifaceCalled reaches the complex128 requirement through dispatch: red BY
// DESIGN at frontend-export (the body constructs a complex value — FR-15).
func ifaceCalled() bool {
	var k Kinder = Yes{k: 1}
	return k.OverflowComplex(complex(2, 0))
}

func mkComplex(n int) complex128 { return complex(float64(n), 0) }

// funcUncalled: a plain func returning complex128 is DECLARED beside the
// subject and never called — an arity stub; the subject lowers.
func funcUncalled() int { return 41 + 1 }

// funcCalled calls it: red BY DESIGN (the value is complex — FR-15).
func funcCalled() float64 { return real(mkComplex(3)) }

// methodUncalled: a METHOD with complex128 in its signature (the shape that
// was a whole-export kill: a method stub must carry its real signature) is
// declared and never called; its healthy sibling `Kind` lowers.
func methodUncalled() int { return Yes{k: 5}.Kind() }

// methodCalled calls the complex-signature method: red BY DESIGN.
func methodCalled() bool { return Yes{k: 1}.OverflowComplex(complex(0, 1)) }

func main() {
	println(ifaceUncalled(), ifaceCalled(), funcUncalled(), funcCalled(), methodUncalled(), methodCalled())
}
