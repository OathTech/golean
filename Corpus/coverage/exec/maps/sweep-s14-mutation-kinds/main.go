package main

// S14 sweep (the defect-neighbourhood campaign, lane sweep/s14-map-iter,
// 2026-10-27; shape «map iteration over a mutating map», members BUG-005 and
// BUG-088): the mutation KINDS at the pick, int keys, three start entries.
// Every observation is ORDER-INDEPENDENT — per-key production counts
// (c1*1000 + c2*100 + c3*10 + the fourth digit), sums, lengths — never the
// order itself, with a runaway guard (-1) so an over-producing machine is
// visible rather than fuel-out.
//
// spec#For_statements (range clause, maps): an entry removed before being
// reached is NOT produced (forced); an entry created during the iteration MAY
// be produced or skipped (latitude, per entry); an entry present throughout
// is produced exactly once (forced). The machine's frame is entry-ID based
// (B1 stamps): a deleted-then-re-created key is a NEW entry (I-1 / L-012).

// delete-unreached: at the first production delete the next key in the
// cyclic order 1→2→3→1 — an unreached key, never produced. Strict cut: two
// productions, the deleted key's count 0, len 2.
func s14DeleteUnreached() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n, u := 0, 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			u = k%3 + 1
			delete(m, u)
		}
	}
	if c[u] != 0 || c[1]+c[2]+c[3] != 2 {
		return -5
	}
	return n*10 + len(m)
}

// delete-reached: delete the FIRST-produced key at the second production —
// no production changes; len 2.
func s14DeleteReached() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n, k0 := 0, 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			k0 = k
		}
		if n == 2 {
			delete(m, k0)
		}
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// delete-unreached-readd: delete an unreached key and re-add it in the same
// iteration: the re-created entry is NEW — produced at most once, maybe
// never. Strict cut: the two surviving start keys once each, the re-created
// at most once, len 3.
func s14DeleteUnreachedReadd() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n, u := 0, 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			u = k%3 + 1
			delete(m, u)
			m[u] = u + 10
		}
	}
	if c[u] > 1 || c[1]+c[2]+c[3]-c[u] != 2 {
		return -5
	}
	return 10 + len(m)
}

// delete-reached-readd-later: the first-produced key is deleted at the
// second production and re-added at the third: the re-created entry may be
// produced AGAIN (count 2) or skipped. Admitted set {1113, 1123, 1213, 2113}.
func s14DeleteReachedReaddLater() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n, k0 := 0, 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			k0 = k
		}
		if n == 2 {
			delete(m, k0)
		}
		if n == 3 {
			m[k0] = k0 + 10
		}
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// update-current: the current key's value is rewritten after its production
// (the bound v is the pre-update value; the rewrite is read back afterwards).
func s14UpdateCurrent() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	sum, n := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		m[k] = v * 10
	}
	return sum*1000 + m[1] + m[2] + m[3]
}

// update-unreached: at the first production every OTHER entry's value is set
// to 100; their later productions read the live value. Strict cut: the sum
// minus the first value is 200, three productions.
func s14UpdateUnreached() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	sum, first, n := 0, 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		if n == 1 {
			first = v
			for u := 1; u <= 3; u++ {
				if u != k {
					m[u] = 100
				}
			}
		}
	}
	return (sum-first)*10 + n
}

// update-keeps-mandatory: an UPDATE of every entry at the first production
// keeps the entries mandatory (same stamps) — all three are produced. Strict
// cut: three productions, the two later ones read the updated values.
func s14UpdateKeepsMandatory() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	sum, first, n := 0, 0, 0
	for _, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		if n == 1 {
			first = v
			m[1] = 10
			m[2] = 20
			m[3] = 30
		}
	}
	// the two later productions read 10*key: sum - first + 10*first = 60
	return n*100 + (sum - first + 10*first)
}

// insert-one: a key created at the first production may be produced or
// skipped (size 3; the size-1 twin is maps/added-entry-count). Admitted set
// {1110, 1111}.
func s14InsertOne() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			m[4] = 4
		}
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + c[4]
}

// insert-two: two keys created at the first production, each independently
// produced or skipped. Admitted set {11100, 11101, 11110, 11111}.
func s14InsertTwo() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			m[4] = 4
			m[5] = 5
		}
	}
	return c[1]*10000 + c[2]*1000 + c[3]*100 + c[4]*10 + c[5]
}

// clear-reinsert-same: clear at the first production, then re-insert the
// same three keys: no entry stays mandatory (the stop is legal at once); each
// re-inserted entry is NEW and may be produced at most once — including the
// first-produced key again. Admitted set: the first key once plus any subset
// of the three re-created entries, len 3 — 19 members.
func s14ClearReinsertSame() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			clear(m)
			m[1] = 11
			m[2] = 12
			m[3] = 13
		}
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// clear-insert-other: clear at the first production, then insert two
// different keys. Strict cut: the first key once, the other start keys never,
// each new key at most once, len 2.
func s14ClearInsertOther() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			clear(m)
			m[7] = 7
			m[8] = 8
		}
	}
	if c[1]+c[2]+c[3] != 1 || c[7] > 1 || c[8] > 1 {
		return -5
	}
	return 10 + len(m)
}

// insert-delete-same-iteration: a key created and deleted within one
// iteration is never a candidate at any pick.
func s14InsertDeleteSameIteration() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		m[9] = 9
		delete(m, 9)
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + c[9]
}

// insert-delete-later: a key created at the first production and deleted at
// the second may be produced at the second pick or not. Admitted set
// {1110, 1111}.
func s14InsertDeleteLater() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			m[9] = 9
		}
		if n == 2 {
			delete(m, 9)
		}
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + c[9]
}

// delete-all-reinsert-all: every key deleted then re-inserted at the first
// production (a clear by deletes). Strict cut as clear-insert-other's: the
// first key once from the start set, each re-created entry at most once,
// len 3.
func s14DeleteAllReinsertAll() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			delete(m, 1)
			delete(m, 2)
			delete(m, 3)
			m[1] = 1
			m[2] = 2
			m[3] = 3
		}
	}
	if c[1] > 2 || c[2] > 2 || c[3] > 2 || c[1]+c[2]+c[3] > 4 || c[1]+c[2]+c[3] < 1 {
		return -5
	}
	return 10 + len(m)
}

func main() {
	println(s14DeleteUnreached())
	println(s14DeleteReached())
	println(s14DeleteUnreachedReadd())
	println(s14DeleteReachedReaddLater())
	println(s14UpdateCurrent())
	println(s14UpdateUnreached())
	println(s14UpdateKeepsMandatory())
	println(s14InsertOne())
	println(s14InsertTwo())
	println(s14ClearReinsertSame())
	println(s14ClearInsertOther())
	println(s14InsertDeleteSameIteration())
	println(s14InsertDeleteLater())
	println(s14DeleteAllReinsertAll())
}
