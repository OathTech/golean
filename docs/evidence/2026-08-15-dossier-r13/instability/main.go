// R13 probe: sort.Slice is documented NOT stable. Sort 64 records by
// key (16 records per key); check whether equal-key records keep
// their input order. Also the int-kind contrast: for a []int, equal
// elements are indistinguishable, so instability is unobservable.
package main

import "sort"

type rec struct{ key, id int }

func main() {
	n := 64
	rs := make([]rec, n)
	for i := 0; i < n; i++ {
		rs[i] = rec{key: i % 4, id: i}
	}
	sort.Slice(rs, func(i, j int) bool { return rs[i].key < rs[j].key })
	inversions := 0
	for k := 1; k < n; k++ {
		if rs[k-1].key == rs[k].key && rs[k-1].id > rs[k].id {
			inversions++
		}
	}
	println("equal-key inversions after sort.Slice:", inversions)
	println("stable?", inversions == 0)

	// contrast: sort.SliceStable preserves order
	for i := 0; i < n; i++ {
		rs[i] = rec{key: i % 4, id: i}
	}
	sort.SliceStable(rs, func(i, j int) bool { return rs[i].key < rs[j].key })
	inv2 := 0
	for k := 1; k < n; k++ {
		if rs[k-1].key == rs[k].key && rs[k-1].id > rs[k].id {
			inv2++
		}
	}
	println("SliceStable inversions:", inv2)
}
