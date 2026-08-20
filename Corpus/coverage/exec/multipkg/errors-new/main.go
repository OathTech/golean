package main

// errors.New in an IMPORTED SOURCE package (multipkg edge of G-2/H-10):
// raft's sentinels live in non-main units (raft, confchange), so the
// E5 shim must inject PER UNIT — each package that calls errors.New
// gets its own shim declarations (distinct qualified FuncId/TypeId),
// and sentinel identity must survive the package boundary. Upstream
// has ONE errorString type where we mint one per package; the delta is
// unobservable in the modeled subset: == is (dynamic type, value)
// equality and the values are distinct fresh pointers whenever the
// types differ (fidelity argument, docs/raft-w4-log.md item 2).

import (
	"errors"

	"liberr"
)

var errLocal = errors.New("local")

func mpErrIdentityAcross() int {
	e := liberr.Give()
	n := 0
	if e == liberr.ErrShared {
		n += 1
	}
	if liberr.IsShared(e) {
		n += 2
	}
	return n
}

func mpErrDistinctAcross() int {
	if errLocal != liberr.ErrShared && errLocal != nil && liberr.ErrShared != nil {
		return 1
	}
	return 0
}

func mpErrTextAcross() int {
	return len(liberr.ErrShared.Error())
}

func main() {
	println(mpErrIdentityAcross(), mpErrDistinctAcross(), mpErrTextAcross())
}
