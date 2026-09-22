package main

// E5BASSERT (Stage E5, family E5b): `v, ok = iv.(int)` — the comma-ok TYPE ASSERTION as a
// two-binder `wide` body (`Stmt.typeAssert` with the binder cells as its targets; a pure op that
// never fails), the two plain targets as sibling plans. A singleton (7): the decoder's arm and its
// mutants are the point; the frontend's own lowering of this call-free sweep is the legacy path.
func e5bassert() int {
	var iv interface{} = 7
	var v int
	var ok bool
	v, ok = iv.(int)
	if ok {
		return v
	}
	return 0
}

func main() { println(e5bassert()) }
