// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// Spurious-distinction cells across FILES and IMPORT ALIASES: one package imported under two
// aliases in two files is one package; a generic type instantiated inside its own package and
// in main is one type; two files' same-named local types are two types; two packages' local
// types of the same name are two types.

import ri "red/inner"

// extra.go imports red/inner as `zz` and blue/inner as `bb`.

// One type through two import aliases in two files.
func multiAliasImport() int {
	s := 0
	if _, ok := fromZZ().(ri.T); ok {
		s += 1
	}
	if _, ok := fromBB().(ri.T); ok {
		s += 10
	}
	if fromZZ() == any(ri.T{Tag: 7}) {
		s += 100
	}
	return s // 101
}

// An instantiation inside its own package vs in main.
func multiInstAcrossPkgs() int {
	s := 0
	if _, ok := ri.MakeGen().(ri.Gen[int]); ok {
		s += 1
	}
	if ri.MakeGen() == any(ri.Gen[int]{}) {
		s += 10
	}
	if _, ok := ri.MakeGenT().(ri.Gen[ri.T]); ok {
		s += 100
	}
	if _, ok := ri.MakeGenT().(ri.Gen[T]); ok {
		s += 1000
	}
	if _, ok := genFromExtra().(ri.Gen[int]); ok {
		s += 10000
	}
	return s // 10101
}

type T struct{ Tag int }

func mkMainL() any { type L int; return L(1) }

// Two files' same-named locals; two packages' same-named locals.
func multiLocals() int {
	s := 0
	if mkMainL() == mkExtraL() {
		s += 1
	}
	if mkMainL() == mkMainL() {
		s += 10
	}
	if ri.Local() == mkMainL() {
		s += 100
	}
	if ri.Local() == ri.Local() {
		s += 1000
	}
	if ri.Local() == extraBlueLocal() {
		s += 10000
	}
	m := map[any]int{}
	m[mkMainL()] = 1
	m[mkExtraL()] = 2
	m[ri.Local()] = 3
	m[extraBlueLocal()] = 4
	return s + len(m)*100000 // 401010
}

// R6 for a local declared in the second file.
func multiReadoutExtra() any { return mkExtraNamed() } // Name() Loc

func main() {}
