// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// A package-level `error` declared in main shadows the universe name INSIDE main only: main's
// `func(error)` is func(main.error), red/inner's is func(error) — two types. (Shadowing `int`
// too breaks the generated oracle harness, which is itself package main — an apparatus limit,
// so that half is out of this cell.)

import ri "red/inner"

type error interface{ Error() string }

func errorShadow() uint8 {
	var s uint8
	var x any = ri.FnErr()
	if _, ok := x.(func(error)); ok {
		s += 1
	}
	var y any = func(error) {}
	if _, ok := y.(func(error)); ok {
		s += 10
	}
	if _, ok := any(ri.FnInt()).(func(int)); ok {
		s += 100
	}
	return s // 110
}

func main() {}
