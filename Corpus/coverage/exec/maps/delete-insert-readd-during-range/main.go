package main

// L-012 / I-1 oracle-exhibited twin of `maps/delete-readd-during-range`
// (added 2026-09-02 at the E9 cross-goroutine slice, from its
// same-goroutine control probe). The ranging goroutine itself deletes
// the FIRST-produced key, inserts one fresh key, then re-inserts the
// deleted key. Under the adopted reading (a deleted-then-re-created key
// is a NEW entry) the re-created key MAY be produced again or MAY be
// skipped; the fresh key is a created entry (may be produced or
// skipped) and does not enter the observable. Observable: how many times
// the first-produced key is produced — admitted set {1 (skipped),
// 2 (produced again)}.
//
// Why this row exists beside `delete-readd-during-range` (whose gc
// sample is always its count-3 member): with ONE intervening insert gc
// re-produces the re-created key in ~87% of runs (17,514/20,000 at size
// 3; the sweep over 0..8 inserts and the size-8 control — never — are in
// docs/evidence/2026-09-02_e9-cross-goroutine-prune/
// gc-same-goroutine-insert.txt and gc-insert-sweep.txt). So the
// re-production member of the I-1 envelope, which L-012's original
// oracle data (400/400 never, incl. forced growth) could not exhibit, is
// gc-EXHIBITED here: both members are observed, the row is a two-sided
// membership pin on the reading.
func mapDeleteInsertReAddDuringRange() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	kcount := 0
	first := true
	k0 := 0
	for k := range m {
		if first {
			first = false
			k0 = k
			kcount++
			delete(m, k)
			m[101] = 101
			m[k] = k + 10
			continue
		}
		if k == k0 {
			kcount++
		}
	}
	return kcount
}

func main() {
	println(mapDeleteInsertReAddDuringRange())
}
