package main

// Stage E of the evaluation-order model v2.1, family E2 (lane core/unseq-stage-e-0921,
// 2026-09-21): POINTERS, FIELDS and MAPS as occurrences. A dereference `*p`, a field
// selection `p.f` and a map element `m[k]` are mutable reads — READ occurrences of the
// `unseq` graph, spec-unsequenced against a sibling call (spec#Order_of_evaluation: «the
// order of those events compared to the evaluation and indexing of x and the evaluation
// of y and z is not specified»); as compound targets their identity is a FROZEN plan —
// the pointer VALUE, the struct's address, the map VALUE and key VALUE — shared by the
// load and the phase-2 store (v2.1 §3.4), so a call that redirects the pointer or rebinds
// the map variable between the plan and the store cannot produce a hybrid. References:
// enumerate.py E2a/E2c/E2e/E2f (docs/evidence/2026-09-16_eval-order-v2-spike/outcomes.txt);
// the hand-built and native wires Tests/unseq-wire/{e2ptr,e2map}.json and native-e2fld.json
// certify the sets over the wire; these rows sample gc (call-first on every row) into them.
// BUG-104's map row (builtins/e13-sibling-panic-order/map-compound-index-key-vs-call) is this
// family's observed-∉-modeled fix and stays in its package.

type P struct{ f int }

func wit(x int) int { println("wit", x); return x }

func setVia(p *int) int { *p = 2; return 0 }
func setF(q *P) int { q.f = 2; return 0 }
func setM(m map[int]int) int { m[1] = 2; return 0 }

// E2a: *p + setVia(p) — the dereference before the call reads 1, after it 2 (gc's). {1, 2}.
func derefVsCall() int {
	x := 1
	p := &x
	return *p + setVia(p)
}

// E2b: q.f + setF(q) — a field read through a pointer. {1, 2}; gc 2.
func fieldVsCall() int {
	q := &P{f: 1}
	return q.f + setF(q)
}

// E2c: m[1] + setM(m) — a map element read. {1, 2}; gc 2.
func mapreadVsCall() int {
	m := map[int]int{1: 1}
	return m[1] + setM(m)
}

// E2e: *p += mut() with mut redirecting the captured p (x = 10 → 11, or y = 100 → 101).
// {11100, 10101}; the hybrids absent.
func derefCompoundRedirect() int {
	x, y := 10, 100
	p := &x
	mut := func() int { p = &y; return 1 }
	*p += mut()
	return x*1000 + y
}

// E2h: q.f += mut() with mut redirecting the captured q (a.f 10 → 11, or b.f 100 → 101).
// {11100, 10101}.
func fieldCompoundRedirect() int {
	a, b := &P{f: 10}, &P{f: 100}
	q := a
	mut := func() int { q = b; return 1 }
	q.f += mut()
	return a.f*1000 + b.f
}

// E2f: m[1] += mut() with mut rebinding the captured m to m2 (old[1] 10 → 11, or m2[1]
// 100 → 101). {11100, 10101}.
func mapCompoundRebind() int {
	m := map[int]int{1: 10}
	m2 := map[int]int{1: 100}
	old := m
	mut := func() int { m = m2; return 1 }
	m[1] += mut()
	return old[1]*1000 + m[1]
}

// A field read on a PRIVATE struct variable beside a call: a stable read (the call cannot
// reach s) — legacy by the trigger, a strict control.
func fieldPrivateVsCall() int {
	var s P
	s.f = 1
	return s.f + wit(1)
}

// A map assignment on private atoms beside a call: the plan checks nothing and reads
// nothing — legacy by the trigger (no non-event occurrence), a strict control.
func mapAssignPlainVsCall() int {
	m := map[int]int{}
	m[1] = wit(5)
	return len(m) + m[1]
}

func main() {
	println(derefVsCall())
	println(fieldVsCall())
	println(mapreadVsCall())
	println(derefCompoundRedirect())
	println(fieldCompoundRedirect())
	println(mapCompoundRebind())
	println(fieldPrivateVsCall())
	println(mapAssignPlainVsCall())
}
