package main

import "iter"

// FR-4 RESIDUAL pin #2 (fr4-rowm audit fix round A5, 2026-09-04): an
// instantiated GENERIC TYPE whose FIELD type does not lower — `iter.Seq[T]`
// at T = int, an imported generic instantiation (FR-23) — reached from a
// HEALTHY body (a zero-valued local): the TypeDef stencil in mono.go flushTypeInsts emits the
// field type in BODY mode (no opaque window for a TypeDef), the refusal has
// no per-declaration quarantine, and the WHOLE export refuses (FR-26's
// neighbourhood: the struct-field kill, here at an instantiation). RED BY
// DESIGN at frontend-export. Flips when FR-26's marker-TypeDef plan lands
// (or FR-23/FR-12 make iter.Seq a value) — retarget then, never let go
// green silently.

type holder[T any] struct {
	items []T
	it    iter.Seq[T]
}

func (h holder[T]) size() int { return len(h.items) }

// A zero-valued local of the instantiation: the BODY mentions holder[int]
// only as a named type (no field is emitted here — a composite literal
// would emit the field types inside the body and quarantine `healthy`
// per declaration instead, measured 2026-09-04), so the field refusal
// fires in the TypeDef stencil of the mono drain — the whole-export kill.
func healthy() int {
	var h holder[int]
	return h.size() + 3 // 3 — never touches it
}

func main() { println(healthy()) }
