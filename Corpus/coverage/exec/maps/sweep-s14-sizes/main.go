package main

// S14 sweep (lane sweep/s14-map-iter, 2026-10-27; members BUG-005, BUG-088):
// map SIZES under mutation — empty and nil (no iteration happens), one entry
// (the delete-re-add tail, the current's update), twelve entries (past gc's
// 8-slot small group, so gc iterates a table and grows it mid-iteration).
// The twelve-entry rows are strict with order-invariant observations; their
// picks outrun the fixed invariance streams, so each declares depth=64
// (4·11 wide picks rounded up to the power of two, min 64).

// empty-insert: no production, so the insert never runs.
func s14EmptyInsert() int {
	m := map[int]int{}
	n := 0
	for k := range m {
		n++
		m[k+1] = 1
	}
	return n*10 + len(m)
}

// nil-delete: a nil map ranges zero times.
func s14NilDelete() int {
	var m map[int]int
	n := 0
	for k := range m {
		n++
		delete(m, k)
	}
	return 10 + n*10 + len(m)
}

// one-delete-readd: one entry deleted and re-created at every production —
// the genuinely unbounded tail, truncated at five (-1 an admitted member):
// {1, 2, 3, 4, 5, -1}.
func s14OneDeleteReadd() int {
	m := map[int]int{1: 1}
	n := 0
	for k := range m {
		n++
		if n > 5 {
			return -1
		}
		delete(m, k)
		m[k] = k
	}
	return n
}

// one-update-current: the single entry's value rewritten after its production.
func s14OneUpdateCurrent() int {
	m := map[int]int{1: 1}
	sum := 0
	for k, v := range m {
		m[k] = v + 10
		sum += v
	}
	return sum*10 + m[1]
}

func twelve() map[int]int {
	m := map[int]int{}
	for i := 1; i <= 12; i++ {
		m[i] = i
	}
	return m
}

// many-delete-current: twelve entries, the current deleted at every production.
func s14ManyDeleteCurrent() int {
	m := twelve()
	n := 0
	for k := range m {
		n++
		if n > 20 {
			return -1
		}
		delete(m, k)
	}
	return n*10 + len(m)
}

// many-delete-evens: at the first production every even key is deleted —
// the unreached ones are never produced; the first production itself may
// have been an even key: {66, 76}.
func s14ManyDeleteEvens() int {
	m := twelve()
	n := 0
	for range m {
		n++
		if n > 20 {
			return -1
		}
		if n == 1 {
			for i := 2; i <= 12; i += 2 {
				delete(m, i)
			}
		}
	}
	return n*10 + len(m)
}

// many-update-unreached: at the first production every other value becomes
// 100; the eleven later productions all read it.
func s14ManyUpdateUnreached() int {
	m := twelve()
	n, hundred := 0, 0
	for k, v := range m {
		n++
		if n > 20 {
			return -1
		}
		if v == 100 {
			hundred++
		}
		if n == 1 {
			for i := 1; i <= 12; i++ {
				if i != k {
					m[i] = 100
				}
			}
		}
	}
	return n*100 + hundred
}

// many-clear: twelve entries cleared at the first production.
func s14ManyClear() int {
	m := twelve()
	n := 0
	for range m {
		n++
		if n > 20 {
			return -1
		}
		clear(m)
	}
	return n*10 + len(m)
}

// many-growth: six keys inserted at the first production of twelve (a gc
// table growth mid-iteration): every start key exactly once, no created
// entry twice, at most six created produced: 12*10 + len/10 = 121.
func s14ManyGrowth() int {
	m := twelve()
	c := map[int]int{}
	n, start, fresh := 0, 0, 0
	for k := range m {
		n++
		if n > 30 {
			return -1
		}
		c[k]++
		if k <= 12 {
			start++
			if c[k] > 1 {
				return -2
			}
		} else {
			fresh++
			if c[k] > 1 {
				return -3
			}
		}
		if n == 1 {
			for i := 101; i <= 106; i++ {
				m[i] = i
			}
		}
	}
	if fresh > 6 {
		return -4
	}
	return start*10 + len(m)/10
}

func main() {
	println(s14EmptyInsert())
	println(s14NilDelete())
	println(s14OneDeleteReadd())
	println(s14OneUpdateCurrent())
	println(s14ManyDeleteCurrent())
	println(s14ManyDeleteEvens())
	println(s14ManyUpdateUnreached())
	println(s14ManyClear())
	println(s14ManyGrowth())
}
