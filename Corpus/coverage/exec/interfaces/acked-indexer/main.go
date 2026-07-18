package main

// A faithful reduction of quorum.AckedIndexer: an interface whose method
// returns two values, satisfied by a defined map type, dispatched dynamically
// and consumed via comma-ok.

type Index uint64

type ackedIndexer interface {
	ackedIndex(id uint64) (Index, bool)
}

type mapAckIndexer map[uint64]Index

func (m mapAckIndexer) ackedIndex(id uint64) (Index, bool) {
	idx, ok := m[id]
	return idx, ok
}

func ackedIndexerHit() int {
	var l ackedIndexer = mapAckIndexer{1: 10, 2: 20}
	v, ok := l.ackedIndex(2)
	if ok {
		return int(v)
	}
	return -1
}

func ackedIndexerMiss() int {
	var l ackedIndexer = mapAckIndexer{1: 10}
	v, ok := l.ackedIndex(9)
	if !ok {
		return 1000 + int(v)
	}
	return -1
}
