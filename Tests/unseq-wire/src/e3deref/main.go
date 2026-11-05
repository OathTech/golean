package main

// E3DEREF (Stage E, family E3 — BUG-391's fix, 2026-11-05): a POINTER-receiver method called on the
// parenthesised dereference `(*p).bump()` beside a VALUE-receiver call `(*p).sum()`. The receiver
// address `&*p` is an `addr-of-deref` occurrence (spec#Address_operators' nil assertion: no read,
// no memory touched). The lowering admitted the spelling and emitted the head; the decoder's
// fragment refused it, so the whole wire was refused by name (rows
// methods/sweep-s17-unseq-deref-receiver/*). The calls are E1-ordered (sum, then bump) and sum's
// receiver copy precedes sum's call, so the set is gc's one value: 2*10 + 2 = 22.
type pt struct{ x, y int }

func (p pt) sum() int   { return p.x + p.y }
func (p *pt) bump() int { p.x++; return p.x }

func e3deref() int {
	p := &pt{1, 1}
	return (*p).sum()*10 + (*p).bump()
}

// E3DEREFNIL: the `addr-of-deref` occurrence FAILING. `p` is captured by wit, which sets it to nil,
// so p's read (a READ occurrence of a mutable location) is unsequenced against wit's call: read
// before wit → `&*p` holds, bump → 1 + 2 = 3; after → nil → the nil assertion panics (gc's: the
// call operands before the receiver's evaluation). {3, panic}.
func e3derefnil() int {
	p := &pt{1, 1}
	wit := func() int { p = nil; return 1 }
	return wit() + (*p).bump()
}

func main() { println(e3deref(), e3derefnil()) }
