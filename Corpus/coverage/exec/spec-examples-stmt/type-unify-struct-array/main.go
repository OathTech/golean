package main

// spec#Type_unification block Type_unification-1-8c22e47c: the type
// equation [10]struct{ elem P, list []P } =A [10]struct{ elem string;
// list []string } unifies with the inference map P -> string (the
// spec walks the unification: same-length arrays unify if element
// types unify; structs unify field-by-field; elem gives P = string;
// list then checks consistently).
// Adaptation: the block is inference META-NOTATION (=A is the
// unification relation, and the spec text itself uses a comma where
// Go needs a semicolon); the executable pin is the CONSEQUENCE — a
// generic function over [10]struct{ elem P; list []P } called with a
// [10]struct{ elem string; list []string } value infers P = string
// without explicit instantiation, and the inferred-P results flow
// back out. Expected: ("elem3", 2).

func tuFirst[P any](x [10]struct {
	elem P
	list []P
}) (P, int) {
	return x[3].elem, len(x[3].list)
}

func typeUnifyStructArray() (string, int) {
	var x [10]struct {
		elem string
		list []string
	}
	x[3].elem = "elem3"
	x[3].list = []string{"a", "b"}
	return tuFirst(x) // type inference must solve P ➞ string
}

func main() {
	typeUnifyStructArray()
}
