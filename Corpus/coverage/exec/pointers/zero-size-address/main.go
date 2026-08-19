package main

// The zero-size address-identity LATITUDE (audit fix round F1,
// 2026-08-19; latitude inventory R15).
//
// spec#Size_and_alignment_guarantees: "Two distinct zero-size
// variables may have the same address in memory." and
// spec#Comparison_operators: "Pointers to distinct zero-size variables
// may or may not be equal." — a genuine two-member spec latitude whose
// observable is plain pointer equality, in-language, no unsafe needed.
//
// gc at the pin (go1.26.5, artifacts/probe/zerosize, scratch) is
// NON-single-valued across shapes: two non-escaping stack variables
// get DISTINCT addresses (0), two escaping/heap-allocated zero-size
// variables both get runtime.zerobase and compare EQUAL (1). The
// machine allocates a fresh cell per variable and answers 0 (distinct)
// on every shape — a conforming member of the envelope, deterministic.
//
// So the two rows below pin BOTH sides of the boundary:
//   - stack-distinct is GREEN: machine and gc realize the same member.
//     It version-tracks gc's stack realization, not a forced point —
//     if a toolchain bump merges stack zero-size variables, the row
//     goes red and the R15 record is what gets revisited.
//   - escaped-same is RED (differential, machine 0 vs go 1): the
//     machine's never-same singleton excludes gc's exhibited heap
//     member. NOT a bug — both answers conform; the red is the
//     version-tracked deviation record (the init/hidden-dep-order
//     class), disposition `latitude` in baselines/untriaged-ids,
//     re-envelope obligation at W3.2 (inventory R15).

type zeroSized struct{}

// stackDistinct: two non-escaping zero-size variables. gc: distinct
// (0). Machine: distinct (0).
func stackDistinct() int {
	var a, b zeroSized
	pa, pb := &a, &b
	if pa == pb {
		return 1
	}
	return 0
}

var zsSinkA, zsSinkB *zeroSized

// escapedSame: the same comparison with both variables escaping
// through package-level sinks. gc: both land on runtime.zerobase,
// equal (1). Machine: fresh cells, distinct (0) — the pinned
// latitude divergence.
func escapedSame() int {
	var a, b zeroSized
	zsSinkA, zsSinkB = &a, &b
	if zsSinkA == zsSinkB {
		return 1
	}
	return 0
}

func main() {
	println(stackDistinct(), escapedSame())
}
