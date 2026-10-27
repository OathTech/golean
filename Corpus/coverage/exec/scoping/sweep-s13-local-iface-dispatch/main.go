package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13 — BUG-301, born red:
// a function-LOCAL named interface type whose method is DISPATCHED. The
// local type declaration mints the interface's dispatch entries
// (emitGenDeclTypes, joined to the method table after the last mono drain)
// and the dispatch site records the called method for the anchor pass of
// emitProgram, which deduplicates against the PACKAGE-LEVEL entries only —
// so the entry is minted twice and the decoder refuses the WHOLE wire
// (`duplicate function id $method$…`) on a legal program. Three forms: a
// local `error` interface (B11), a local getter re-asserted at a package
// interface (J9), the same local name in two functions. Expected = gc.

type Outer struct{ v int }

func (o Outer) Get() int { return o.v }

type Getter interface{ Get() int }

type coded struct{ c int }

func (c coded) Code() int { return c.c }

// B11: a local interface type named error, satisfied by a package type.
func errorLocalIface() int {
	type error interface{ Code() int }
	var e error = coded{5}
	return e.Code() // 5
}

// J9
func localIfaceSatisfied() int {
	type getter interface{ Get() int }
	var g getter = Outer{6}
	if _, ok := any(g).(Getter); ok {
		return g.Get() * 2 // 12
	}
	return -1
}

func a() int {
	type getter interface{ Get() int }
	var g getter = Outer{1}
	return g.Get()
}

func b() int {
	type getter interface{ Get() int }
	var g getter = Outer{2}
	return g.Get()
}

// A local interface of one name in two functions, each dispatching.
func localIfaceTwoFuncs() int { return a()*10 + b() } // 12

func main() { println(errorLocalIface(), localIfaceSatisfied(), localIfaceTwoFuncs()) }
