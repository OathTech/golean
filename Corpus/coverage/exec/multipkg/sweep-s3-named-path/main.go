// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K2 named types keyed by import PATH: red/inner.T, blue/inner.T and main.T share a name and
// a shape; each is identical only to itself. R1 and R2 are pinned rows; these are R3–R8.

import (
	bi "blue/inner"
	ri "red/inner"
)

type T struct{ Tag int }

func (T) Name() string { return "main" }

type Namer interface{ Name() string }

// R3: a type switch over the three same-named types.
func namedPathSwitch() int {
	r := 0
	for _, v := range []any{ri.Make(1), bi.Make(2), T{3}} {
		d := 0
		switch v.(type) {
		case ri.T:
			d = 1
		case bi.T:
			d = 2
		case T:
			d = 3
		}
		r = r*10 + d
	}
	return r // 123
}

// R4: == of boxes.
func namedPathEqual() int {
	s := 0
	if any(ri.Make(1)) == any(bi.Make(1)) {
		s += 1
	}
	if any(ri.Make(1)) == any(ri.Make(1)) {
		s += 10
	}
	if any(T{1}) == any(ri.Make(1)) {
		s += 100
	}
	if any(T{1}) == any(T{1}) {
		s += 1000
	}
	return s // 1010
}

// R5: map[any] keys.
func namedPathMapKeys() int {
	m := map[any]int{}
	m[ri.Make(1)] = 1
	m[bi.Make(1)] = 2
	m[T{1}] = 3
	m[ri.Make(1)] = 4
	return len(m)*10 + m[ri.Make(1)] // 34
}

// R6: the readout's dynamic name (reflect Name() = "T" for each).
func namedPathReadout() (any, any, any) {
	return ri.Make(1), bi.Make(2), T{3}
}

// R7: dispatch through an interface reaches each package's body.
func namedPathDispatch() string {
	ns := []Namer{ri.Make(0), bi.Make(0), T{}}
	s := ""
	for _, n := range ns {
		s += n.Name()
	}
	return s // redbluemain
}

// R8: the path identity inside slices, pointers and maps.
func namedPathWrappers() int {
	s := 0
	if _, ok := any([]ri.T{}).([]bi.T); ok {
		s += 1
	}
	if _, ok := any([]ri.T{}).([]ri.T); ok {
		s += 10
	}
	if _, ok := any(&ri.T{}).(*bi.T); ok {
		s += 100
	}
	if _, ok := any(&ri.T{}).(*T); ok {
		s += 1000
	}
	if _, ok := any(map[string]ri.T{}).(map[string]bi.T); ok {
		s += 10000
	}
	if _, ok := any(map[string]ri.T{}).(map[string]ri.T); ok {
		s += 100000
	}
	return s // 100010
}

// K3×K2: a function-local T beside the imported T of the same name.
func localVsImported() int {
	type T int
	s := 0
	var x any = T(1)
	if _, ok := x.(ri.T); ok {
		s += 1
	}
	if _, ok := x.(T); ok {
		s += 10
	}
	var y any = ri.L(1)
	if _, ok := y.(T); ok {
		s += 100
	}
	return s // 10
}

// R2 for a local vs an imported name: gc says "(types from different packages)".
func localVsImportedPanic() int {
	type T struct{ Tag int }
	var x any = T{1}
	return x.(ri.T).Tag
}

func main() {}
