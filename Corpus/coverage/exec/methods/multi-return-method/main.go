package main

// mapAckIndexer mirrors quorum.mapAckIndexer: a method on a defined map type
// that returns two values by forwarding a comma-ok map lookup.

type Index uint64

type mapAckIndexer map[uint64]Index

func (m mapAckIndexer) ackedIndex(id uint64) (Index, bool) {
	idx, ok := m[id]
	return idx, ok
}

func multiReturnMethod() int {
	m := mapAckIndexer{1: 10, 2: 20}
	v1, ok1 := m.ackedIndex(2)
	_, ok2 := m.ackedIndex(9)
	r := 0
	if ok1 {
		r += int(v1)
	}
	if !ok2 {
		r += 1000
	}
	return r
}
