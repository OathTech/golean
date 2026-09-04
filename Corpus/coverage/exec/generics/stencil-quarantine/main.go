package main

import "reflect"

// FR-4 (2026-09-04, lane fr4-rowm): per-declaration quarantine for method
// STENCILS — a method of a generic type at one receiver instantiation
// whose body does not lower becomes a fail-closed STUB naming the
// instantiation and the inner cause (mono.go flushTypeInsts →
// quarantinedStencilStub), exactly the H-3 contract for declared methods
// (docs/bugfix-arc-log.md §H-3): the stub stays in the instantiated type's
// method set (satisfaction answers), the rest of the package lowers, and
// only a CALL of the stencil refuses — by name.
//
// Before FR-4 this package refused WHOLE (`sibling` was the FRONTIER PIN,
// born red at slice 6): one unlowerable stencil took every innocent
// subject down. The instantiation s6box[int] is USED, so the stencil set
// flushes; render's reflect.TypeOf is the unlowerable construct.
//
// WHY `reflect.TypeOf` (JC-17, THIRD pick — audit R4-M-1): the unlowerable
// construct is load-bearing — it is what makes the stencil refuse at all.
// `fmt.Sprintf`/`fmt.Sprint` lowered when their desugars landed; the
// lesson is to pick the cause by structural distance from the modeled
// envelope, not by "currently unmodeled". WHY REFLECTION IS FAR: the
// frontend lowers a CLOSED WORLD of statically instantiated types, and
// reflect.TypeOf asks about a value's DYNAMIC type — a question the wire's
// static type channel does not carry (a scope statement about this
// frontend, not a claim that reflection is unmodelable in principle). If
// reflect ever lowers, the red rows here flip LOUDLY and must be
// retargeted, never let go green.
//
// The interactions each row pins (ledger FR-4):
//   sibling               the export survives; a subject that never
//                         reaches the stencil is green (the FR-4 witness,
//                         FLIPPED)
//   stencil-call-refuses  a direct call of the quarantined stencil refuses
//                         BY NAME (main.s6box[int].render)
//   iface-satisfied       the stub stays in s6box[int]'s method set: the
//                         comma-ok assertion to an interface REQUIRING
//                         render answers true (a dropped entry would answer
//                         a silently wrong false — the H-3 fail-closed
//                         guard)
//   iface-dispatch        dispatch to the stub through the interface
//                         refuses by name, never vanishes
//   transitive-lowers     a stencil reached ONLY through another stencil
//                         (outer[int].val → s6box[int].get) lowers when
//                         its body is fine
//   transitive-call       a lowerable stencil whose body CALLS the
//                         quarantined one lowers itself; the call refuses
//                         at the inner stub, which is the one named
//   dedup-second-body     s6box[int] reached from two bodies, one of them
//                         quarantined (localC6's rollback must not remove
//                         the instantiation the healthy body registered)
//   local-type-c6         the C6 naming refusal (mono.go renderTypeArg: a
//                         function-local defined type as a type argument)
//                         stays a refusal, per DECLARATION — it quarantines
//                         localC6 alone (ledger §5.1 C6, a ratified (c)-pin)

type s6box[T any] struct{ v T }

// render does not lower (reflect.TypeOf): the quarantined stencil.
func (b s6box[T]) render() string { return reflect.TypeOf(b.v).String() }

// get lowers: the healthy sibling stencil of the same instantiation.
func (b s6box[T]) get() T { return b.v }

// renderer REQUIRES the quarantined method: satisfaction must still hold.
type renderer interface {
	render() string
	get() int
}

// outer reaches s6box only through its own stencils.
type outer[T any] struct{ in s6box[T] }

func (o outer[T]) val() T       { return o.in.get() }
func (o outer[T]) show() string { return o.in.render() }

func stencilSibling() int {
	b := s6box[int]{v: 3}
	return b.v * 3 // 9 — never calls render
}

func stencilCallRefuses() int {
	b := s6box[int]{v: 3}
	return len(b.render()) // gc: len("int") = 3; ours: refused by name
}

func ifaceSatisfied() int {
	var x any = s6box[int]{v: 5}
	if r, ok := x.(renderer); ok {
		return r.get() + 100 // 105 — the stub is IN the method set
	}
	return 0
}

func ifaceDispatch() int {
	var x any = s6box[int]{v: 5}
	r := x.(renderer)
	return len(r.render()) // gc: 3; ours: dispatch lands on the stub, refuses by name
}

func transitiveLowers() int {
	o := outer[int]{in: s6box[int]{v: 7}}
	return o.val() * 2 // 14
}

func transitiveCall() int {
	o := outer[int]{in: s6box[int]{v: 7}}
	return len(o.show()) // gc: 3; ours: outer[int].show lowers, s6box[int].render refuses
}

func dedupSecondBody() int {
	// The SAME instantiation s6box[int] is registered here (healthy) and
	// inside localC6 (quarantined); the quarantine's rollback must undo
	// only its own journal entries.
	b := s6box[int]{v: 11}
	return b.get() + 1 // 12
}

func localC6() int {
	type score int
	b := s6box[score]{v: 4} // C6: gc names this instantiation main.score·1 — refused, not guessed
	b2 := s6box[int]{v: 1}
	return int(b.get()) + b2.get()
}

func main() {
	println(stencilSibling())
	println(ifaceSatisfied())
	println(transitiveLowers())
	println(dedupSecondBody())
}
