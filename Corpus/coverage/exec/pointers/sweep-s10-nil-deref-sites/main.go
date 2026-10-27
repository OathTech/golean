package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10 of the defect-neighbourhood
// campaign (plan §4): the nil-pointer-dereference panic at every indirection SITE
// the member entries (BUG-038 the nil *[N]T store, BUG-056 `&*p`, BUG-063 the
// implicit receiver `&*q`) did not pin — the read/store/compound/incdec forms of
// `*p`, `p.f`, `p[i]`, nested and deep-offset fields, the condition/switch/blank/
// argument positions, the defer and go argument positions (the panic is raised
// at the statement, before anything is registered or spawned), the two
// multi-target orders at the FIELD site, the whole-array and whole-struct copies,
// `**pp`, `*[]T` and `*map` bases, and the no-panic control (`len`/`cap` of a
// nil array pointer are constants). The zero-length two-variable range is
// range/sweep-s10-zero-len-two-vars (born red, BUG-226). spec#Address_operators, #Selectors, #Index_expressions,
// #Assignment_statements, #Defer_statements, #Go_statements, #Length_and_capacity.
// Every expectation computed from `go run` (go1.26.5) before the differential ran.

type ndsInner struct{ f int }

type ndsOuter struct {
	q *ndsInner
	n int
}

type ndsBig struct {
	pad [1024]int64
	f   int
}

var ndsCount int

func ndsSink(x int) { ndsCount += 1000 + x }

func blankDeref() int {
	var p *int
	_ = *p
	return 0
}

func callArgDeref() int {
	var p *int
	ndsSink(*p)
	return ndsCount
}

func ifCondDeref() int {
	var p *int
	if *p == 0 {
		return 1
	}
	return 2
}

func switchDeref() int {
	var p *int
	switch *p {
	case 0:
		return 1
	}
	return 2
}

func derefStore() int {
	var p *int
	*p = 1
	return 0
}

func derefCompound() int {
	var p *int
	*p += 1
	return 0
}

func derefIncdec() int {
	var p *int
	(*p)++
	return 0
}

func fieldStore() int {
	var p *ndsInner
	p.f = 1
	return 0
}

func fieldCompound() int {
	var p *ndsInner
	p.f += 1
	return 0
}

func fieldIncdec() int {
	var p *ndsInner
	p.f++
	return 0
}

func nestedFieldRead() int {
	o := &ndsOuter{n: 3}
	return o.q.f + o.n
}

func nestedFieldStore() int {
	o := &ndsOuter{n: 3}
	o.q.f = 1
	return o.n
}

func deepOffsetRead() int {
	var p *ndsBig
	return p.f
}

func deepOffsetStore() int {
	var p *ndsBig
	p.f = 7
	return 0
}

func arrayElemCompound() int {
	var p *[3]int
	p[0] += 1
	return 0
}

func arrayElemIncdec() int {
	var p *[3]int
	p[1]++
	return 0
}

// The defer ARGUMENT is evaluated at the defer statement: the nil
// dereference panics there, so ndsSink is never registered (count stays
// below 1000), the earlier-registered closure runs during the unwind (+1),
// the statement after the defer never runs (+10 missing). gc: 101.
func deferArgDeref() int {
	var p *int
	ndsCount = 0
	count := 0
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		defer func() { count += 1 }()
		defer ndsSink(*p)
		count += 10
	}()
	return r + count + ndsCount
}

// The go ARGUMENT is evaluated in the spawning goroutine at the go statement:
// the nil dereference panics there, recoverable in the parent; nothing is
// spawned. gc: 100.
func goArgDeref() int {
	var p *int
	ndsCount = 0
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		go ndsSink(*p)
	}()
	return r + ndsCount
}

// len/cap of a nil pointer to array, and len of its indirection, are
// CONSTANTS (spec#Length_and_capacity: the operand is not evaluated). gc: 333.
func lenCapNilArrayPtr() int {
	var p *[3]int
	return len(p)*100 + cap(p)*10 + len(*p)
}

func derefArrayCopy() int {
	var p *[3]int
	a := *p
	return a[0]
}

func derefStructCopy() int {
	var p *ndsInner
	s := *p
	return s.f
}

func doubleDerefInnerNil() int {
	var q *int
	pp := &q
	return **pp
}

func slicePtrDerefIndex() int {
	var sp *[]int
	return (*sp)[0]
}

func mapPtrDerefIndex() int {
	var mp *map[int]int
	return (*mp)[1]
}

// Phase 2 of the assignment stores left to right, each target checked at
// its own store: the nil FIELD target first → x is never stored. gc: 100.
func multiTargetFieldFirst() int {
	var p *ndsInner
	x := 0
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		p.f, x = 1, 2
	}()
	return r + x
}

// The same with the nil field target SECOND: x is stored, then the panic.
// gc: 101 (BUG-038's second-target shape at the field site).
func multiTargetFieldSecond() int {
	var p *ndsInner
	x := 0
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		x, p.f = 1, 2
	}()
	return r + x
}

func main() {}
