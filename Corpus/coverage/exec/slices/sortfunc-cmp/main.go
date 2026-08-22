package main

// slices.SortFunc + cmp.Compare conformance (W4.3 item 1 landing B —
// the W1.2 inheritance, H-5; docs/raft-w43-log.md). Mechanisms:
// cmp.Compare desugars at emit time to kind shims (unsigned/signed/
// string) with explicit conversions; slices.SortFunc emits a call to
// an INJECTED GENERIC insertion-sort shim, stenciled through the
// ordinary mono pipeline at the call's element type.
//
// THE TIE LATITUDE, recorded: upstream SortFunc is "not guaranteed to
// be stable" — any cmp-consistent order conforms. The shim (insertion
// sort) is stable; gc's pdqsort need not be. Every row here is
// TIE-FREE (a total order per cmp) except sort-ties-projected, whose
// OBSERVATION projects only the cmp key — green under ANY conforming
// order on both oracles, which is exactly the envelope quotient.
// Subject site: quorum.MajorityConfig.Describe (two SortFuncs over a
// local tup struct, cmp.Compare keys).

import (
	"cmp"
	"slices"
)

func renderInts(xs []int) string {
	out := ""
	for i, x := range xs {
		if i > 0 {
			out += ","
		}
		d := x
		neg := false
		if d < 0 {
			neg = true
			d = -d
		}
		s := ""
		if d == 0 {
			s = "0"
		}
		for d > 0 {
			s = string(rune('0'+d%10)) + s
			d /= 10
		}
		if neg {
			s = "-" + s
		}
		out += s
	}
	return out
}

func cmpCompareKinds() int {
	type index uint64 // the quorum.Index shape
	a := cmp.Compare(index(3), index(7))
	b := cmp.Compare(uint64(9), uint64(9))
	c := cmp.Compare(-5, 4)
	d := cmp.Compare("b", "a")
	return (a+1)*1000 + (b+1)*100 + (c+1)*10 + (d + 1)
}

func sortFuncInts() string {
	xs := []int{5, 1, 4, 2, 3}
	slices.SortFunc(xs, func(a, b int) int { return cmp.Compare(a, b) })
	return renderInts(xs)
}

func sortFuncReverse() string {
	xs := []int{5, 1, 4, 2, 3}
	slices.SortFunc(xs, func(a, b int) int { return cmp.Compare(b, a) })
	return renderInts(xs)
}

// The MajorityConfig.Describe two-key cmp shape, at a PACKAGE-LEVEL
// struct. The real Describe declares `tup` FUNCTION-LOCALLY, which
// hits the standing local-type-as-type-argument refusal (the C6
// compiler-internal-suffix class) — sortfunc-local-type below pins
// that boundary red; this row pins the two-key semantics green.
type tup struct {
	id  uint64
	idx uint64
}

func sortFuncStructTwoKey() string {
	info := []tup{{3, 10}, {1, 20}, {2, 10}}
	slices.SortFunc(info, func(a, b tup) int {
		if n := cmp.Compare(a.idx, b.idx); n != 0 {
			return n
		}
		return cmp.Compare(a.id, b.id)
	})
	out := []int{}
	for _, t := range info {
		out = append(out, int(t.id))
	}
	return renderInts(out)
}

func sortFuncEmptySingle() string {
	var e []int
	slices.SortFunc(e, func(a, b int) int { return cmp.Compare(a, b) })
	s := []int{7}
	slices.SortFunc(s, func(a, b int) int { return cmp.Compare(a, b) })
	return renderInts(e) + "|" + renderInts(s)
}

// Ties exist; the observation projects the cmp KEY only, so it is
// invariant across every cmp-consistent order — the quotiented row.
type kv struct {
	k int
	v int
}

func sortTiesProjected() string {
	xs := []kv{{2, 100}, {1, 200}, {2, 300}, {1, 400}}
	slices.SortFunc(xs, func(a, b kv) int { return cmp.Compare(a.k, b.k) })
	keys := []int{}
	for _, x := range xs {
		keys = append(keys, x.k)
	}
	return renderInts(keys)
}

// ---- fail-closed boundary row (red BY DESIGN) ----

// The REAL MajorityConfig.Describe shape: the element struct is
// function-local, and a local defined type as a type argument refuses
// (gc renders these with a compiler-internal unique suffix — the C6
// ratified class). This row keeps that intersection visible; the
// subject's Describe stays quarantined on exactly this cause.
func sortFuncLocalType() string {
	type ltup struct{ id uint64 }
	info := []ltup{{2}, {1}}
	slices.SortFunc(info, func(a, b ltup) int { return cmp.Compare(a.id, b.id) })
	out := []int{}
	for _, t := range info {
		out = append(out, int(t.id))
	}
	return renderInts(out)
}

// ---- R4-M-3 (audit fix round): the two UNPINNED narrowings, pinned
// as red-by-design refusal rows (probe r4-p5 — gc handles both). ----

type namedIDs []uint64

// RED BY DESIGN: slices.SortFunc's `S ~[]E` freedom is NARROWED to
// S == []E exactly (genericshim.go names the bound); a NAMED slice
// type refuses. gc: sorts it fine (123).
func sortFuncNamedSlice() int {
	x := namedIDs{3, 1, 2}
	slices.SortFunc(x, func(a, b uint64) int { return cmp.Compare(a, b) })
	return int(x[0])*100 + int(x[1])*10 + int(x[2])
}

// RED BY DESIGN: cmp.Compare's FLOAT arm is excluded (the NaN
// ordering is cmp.Compare-specific latitude nothing in scope needs);
// SortFunc itself admits []float64, so the refusal lands on the
// comparator. gc: 2.
func sortFuncFloatCompare() int {
	x := []float64{2.0, 1.0}
	slices.SortFunc(x, func(a, b float64) int { return cmp.Compare(a, b) })
	return len(x)
}

func main() {
	println(cmpCompareKinds(), sortFuncInts(), sortFuncReverse(),
		sortFuncStructTwoKey(), sortFuncEmptySingle(), sortTiesProjected(),
		sortFuncLocalType(), sortFuncNamedSlice(), sortFuncFloatCompare())
}
