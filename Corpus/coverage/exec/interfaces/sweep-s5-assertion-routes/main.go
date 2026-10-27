package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The ASSERTION routes over method sets beyond BUG-095's embedding family: an
// interface-to-interface assertion to an UNRELATED interface; a value box
// asserted to an interface whose method has a POINTER receiver (comma-ok
// false; the one-value form panics naming the method); a type switch whose
// pointer-method case comes first; a pointer-to-interface box (an empty
// method set, like `**T`).

type reader interface{ Read() int }
type writer interface{ Write(int) int }
type setter interface{ Set(int) }

type doc struct{ n int }

func (d doc) Read() int       { return d.n }
func (d doc) Write(v int) int { return d.n + v }
func (d *doc) Set(v int)      { d.n = v }

func unrelatedInterfaces() int {
	var r reader = doc{n: 5}
	w, ok := r.(writer) // reader and writer share no method: a runtime check
	r2 := r.(writer)    // the one-value form succeeds
	res := w.Write(1)*100 + r2.Write(2)
	if ok {
		res += 10000
	}
	return res
}

func pointerMethodMissingOk() int {
	var r reader = doc{n: 1}
	_, okVal := r.(setter) // the value box: Set is in *doc's set only
	var p reader = &doc{n: 2}
	s, okPtr := p.(setter)
	res := 0
	if okVal {
		res += 100
	}
	if okPtr {
		s.Set(7)
		res += 10 + p.Read()
	}
	return res
}

func pointerMethodMissingPanic() int {
	var r reader = doc{n: 1}
	s := r.(setter) // panics: interface conversion ... missing method Set
	s.Set(2)
	return r.Read()
}

func typeSwitchOrder() int {
	classify := func(x any) int {
		switch x.(type) {
		case setter:
			return 1
		case reader:
			return 2
		default:
			return 3
		}
	}
	d := doc{n: 1}
	return classify(d)*100 + classify(&d)*10 + classify(1)
}

func pointerToInterfaceNoMethods() int {
	var r reader = doc{n: 3}
	pr := &r
	var x any = pr // *reader carries no methods
	_, ok := x.(reader)
	res := (*pr).Read()
	if ok {
		res += 100
	}
	return res
}

func main() {
	unrelatedInterfaces()
	pointerMethodMissingOk()
	typeSwitchOrder()
	pointerToInterfaceNoMethods()
}
