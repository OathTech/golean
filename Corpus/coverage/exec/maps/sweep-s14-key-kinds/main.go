package main

// S14 sweep (lane sweep/s14-map-iter, 2026-10-27; members BUG-005, BUG-088):
// KEY KINDS under mutation during the range. The frame's produced/start
// sets are entry ids, so the pick is key-blind; the key kind matters at the
// UPDATE path (the entry found by the kind's equality keeps its stamp — a
// missed match would mint a new entry and move len and the sum) and at the
// irreflexive keys (NaN: never found, each insert a new entry, delete a
// no-op; ±0: one entry, its stored key replaced by the update).
//
// The strict rows: delete the CURRENT key at every production and, at the
// first, update every OTHER entry (values start equal at 1) to 100 through
// the kind's own equality: sum = 1 + 100 + 100 = 201, len 0 -> 2010,
// order-invariant. The membership rows carry the NaN / ±0 latitude.

func s14StringKeys() int {
	m := map[string]int{"a": 1, "b": 1, "c": 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			for _, u := range []string{"a", "b", "c"} {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return sum*10 + len(m)
}

func s14FloatKeys() int {
	m := map[float64]int{1.5: 1, 2.5: 1, 3.5: 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			for _, u := range []float64{1.5, 2.5, 3.5} {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return sum*10 + len(m)
}

func s14InterfaceMixedKeys() int {
	m := map[any]int{1: 1, "b": 1, true: 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			for _, u := range []any{1, "b", true} {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return sum*10 + len(m)
}

type pt struct{ a, b int }

func s14StructKeys() int {
	m := map[pt]int{{1, 1}: 1, {2, 2}: 1, {3, 3}: 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			for _, u := range []pt{{1, 1}, {2, 2}, {3, 3}} {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return sum*10 + len(m)
}

func s14ArrayKeys() int {
	m := map[[2]int]int{{1, 1}: 1, {2, 2}: 1, {3, 3}: 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			for _, u := range [][2]int{{1, 1}, {2, 2}, {3, 3}} {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return sum*10 + len(m)
}

func s14PointerKeys() int {
	p1, p2, p3 := new(int), new(int), new(int)
	m := map[*int]int{p1: 1, p2: 1, p3: 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			for _, u := range []*int{p1, p2, p3} {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return sum*10 + len(m)
}

func s14BoolKeys() int {
	m := map[bool]int{true: 1, false: 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			m[!k] = 100
		}
	}
	return sum*10 + len(m)
}

type kint int

func s14DefinedIntKeys() int {
	m := map[kint]int{1: 1, 2: 1, 3: 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			for u := kint(1); u <= 3; u++ {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return sum*10 + len(m)
}

func s14ChannelKeys() int {
	c1, c2, c3 := make(chan int), make(chan int), make(chan int)
	m := map[chan int]int{c1: 1, c2: 1, c3: 1}
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, k)
		if n == 1 {
			for _, u := range []chan int{c1, c2, c3} {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return sum*10 + len(m)
}

// nan-inserted-during-range: a NaN key inserted at each of the first two
// productions is a NEW entry each time (never found), producible or not:
// {12, 23, 33} as n*10 + len.
func s14NanInsertedDuringRange() int {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{1.0: 1}
	n := 0
	for range m {
		n++
		if n > 4 {
			return -1
		}
		if n <= 2 {
			m[nan] = n
		}
	}
	return n*10 + len(m)
}

// nan-delete-noop: delete(m, NaN) during the range finds nothing — the two
// NaN entries and the 1.0 entry are all produced.
func s14NanDeleteNoop() int {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{1.0: 3}
	m[nan] = 1
	m[nan] = 2
	n, sum := 0, 0
	for _, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		delete(m, nan)
	}
	return n*100 + sum*10 + len(m)
}

// nan-clear-mid-range: clear with two NaN entries present at the first
// production, then one NaN insert (a created entry): {11, 21}.
func s14NanClearMidRange() int {
	zero := 0.0
	nan := zero / zero
	m := map[float64]int{1.0: 3}
	m[nan] = 1
	m[nan] = 2
	n := 0
	for range m {
		n++
		if n > 8 {
			return -1
		}
		if n == 1 {
			clear(m)
			m[nan] = 4
		}
	}
	return n*10 + len(m)
}

// signed-zero-update-mid-range: m[-0] = 10 at the first production updates
// the +0 entry — the same entry (still mandatory, produced once) with its
// stored key replaced by -0: produced first (key +0, value 1) or later (key
// -0, value 10): {3001, 3110}.
func s14SignedZeroUpdateMidRange() int {
	posZero := 0.0
	negZero := -posZero
	m := map[float64]int{posZero: 1, 1.0: 2, 2.0: 3}
	n, neg, zv := 0, 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		if n == 1 {
			m[negZero] = 10
		}
		if k == 0 {
			if 1/k < 0 {
				neg++
			}
			zv += v
		}
	}
	return n*1000 + neg*100 + zv
}

// interface-nan-inserted: the NaN-in-interface twin of nan-inserted-during-range.
func s14InterfaceNanInserted() int {
	zero := 0.0
	nan := zero / zero
	m := map[any]int{1: 1}
	n := 0
	for range m {
		n++
		if n > 4 {
			return -1
		}
		if n <= 2 {
			m[nan] = n
		}
	}
	return n*10 + len(m)
}

type fk struct{ f float64 }

// struct-nan-mutated: struct keys holding NaN, mutated at the first
// production — a new NaN entry inserted (may be produced), a NaN delete (a
// no-op), the non-NaN key updated (read live if unreached): {3006, 3033,
// 4010, 4037} as n*1000 + sum.
func s14StructNanKeysMutated() int {
	zero := 0.0
	nan := zero / zero
	m := map[fk]int{}
	m[fk{nan}] = 1
	m[fk{nan}] = 2
	m[fk{1}] = 3
	n, sum := 0, 0
	for _, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		if n == 1 {
			m[fk{nan}] = 4
			delete(m, fk{nan})
			m[fk{1}] = 30
		}
	}
	return n*1000 + sum
}

func main() {
	println(s14StringKeys())
	println(s14FloatKeys())
	println(s14InterfaceMixedKeys())
	println(s14StructKeys())
	println(s14ArrayKeys())
	println(s14PointerKeys())
	println(s14BoolKeys())
	println(s14DefinedIntKeys())
	println(s14ChannelKeys())
	println(s14NanInsertedDuringRange())
	println(s14NanDeleteNoop())
	println(s14NanClearMidRange())
	println(s14SignedZeroUpdateMidRange())
	println(s14InterfaceNanInserted())
	println(s14StructNanKeysMutated())
}
