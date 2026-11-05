// Defect-neighbourhood campaign, shape S29 (synthetic-symbol bookkeeping; members
// BUG-031/027, and BUG-302 fixed in train 28), lane sweep/s28-s29-spelling-symbols,
// 2026-11-05 (docs/2026-10-27_defect-neighbourhood-campaign.md §4). The CONTROL beside
// generics/sweep-s29-lit-typeparam-neighbours: a func literal inside a generic function
// with no parameter and an unnamed T result mentions no parameter object, so it lowers
// on main 12d7a79a where BUG-302 is open; expected = gc go1.26.5.

package main

func gResultOnly[T ~int](v T) T {
	f := func() T { return v }
	return f()
}

func litResultOnlyT() int { return int(gResultOnly(11)) } // 11

func main() { println("litResultOnlyT", litResultOnlyT()) }
