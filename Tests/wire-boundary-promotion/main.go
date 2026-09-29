// Tests/wire-boundary-promotion/main.go — the promotion-record fixture of
// scripts/check-wire-boundary (G-P S1, design note
// docs/2026-09-28_gp-method-promotion-design.md §4/§5; G-P PASSED [USER]
// 2026-09-28, relayed). Every promoted method-set SHAPE the records
// distinguish is present, so one wire carries every record kind the
// byte-level mutants need:
//
//	mid.val    value embed, value receiver            path [{mid, base, false}]        asIs   both sets
//	mid.inc    value embed, pointer receiver           the same hop                     addr   *mid ONLY
//	outer.val  pointer embed then value embed          [{outer, mid, true}, {mid, base, false}]  asIs  both sets
//	outer.inc  the same two hops, pointer receiver     addr from a VALUE root (the pointer hop supplies the address)
//	outer.own  pointer embed to a DECLARED method of mid (mid.own shadows base.own at depth 1)
//	wrapI.val  an embedded INTERFACE field             target {iface: valuer}
//	solo.inc   value embed, pointer receiver           *solo ONLY
//	locked.{Lock,TryLock,Unlock}  embedded sync.Mutex  declaration-only STUBS: unsupported + sig
//
// `probe` answers 42 through the real machine (the positive control): the
// dynamic calls above dispatch through these records — the machine resolves
// each entry from its record and walks the path itself (G-P S2; `wrapI.val`
// re-dispatches on the embedded interface field's value as its own step).
package main

import "sync"

type base struct{ n int }

func (b base) val() int { return b.n }
func (b *base) inc()    { b.n++ }
func (b base) own() int { return 1 }

type mid struct{ base }

func (m mid) own() int { return 2 }

type outer struct{ *mid }
type solo struct{ base }
type valuer interface{ val() int }
type incer interface{ inc() }
type wrapI struct{ valuer }
type locked struct {
	sync.Mutex
	n int
}

func probe() int {
	m := &mid{base{10}}
	var i incer = m // mid.inc through the *mid-only wrapper (addr)
	i.inc()         // 11
	o := outer{m}
	var i2 incer = o // outer.inc: value root, pointer hop, then the field's address
	i2.inc()         // 12
	var v valuer = o // outer.val: field-get, deref, field-get
	var w valuer = wrapI{v}
	s := &solo{base{20}}
	var i3 incer = s
	i3.inc() // 21
	var l locked
	l.Lock() // the static sync op lowers at its site; the stub answers satisfaction only
	l.n = 3
	l.Unlock()
	return v.val() + w.val() + s.val() - l.n // 12 + 12 + 21 - 3
}

func main() { println(probe()) }
