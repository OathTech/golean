// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K15 the sync primitive types are nominal on the machine (`Ty.sync kind`): *sync.Mutex ≢
// *sync.RWMutex ≢ *sync.WaitGroup ≢ *sync.Once.

import "sync"

// R1
func syncAssert() int {
	var mu sync.Mutex
	var rw sync.RWMutex
	var wg sync.WaitGroup
	var once sync.Once
	s := 0
	if _, ok := any(&mu).(*sync.RWMutex); ok {
		s += 1
	}
	if _, ok := any(&mu).(*sync.Mutex); ok {
		s += 10
	}
	if _, ok := any(&rw).(*sync.Mutex); ok {
		s += 100
	}
	if _, ok := any(&wg).(*sync.Once); ok {
		s += 1000
	}
	if _, ok := any(&once).(*sync.Once); ok {
		s += 10000
	}
	if _, ok := any(&mu).(sync.Locker); ok {
		s += 100000
	}
	if _, ok := any(&wg).(sync.Locker); ok {
		s += 1000000
	}
	return s // 110010
}

// R3
func syncSwitch() int {
	var mu sync.Mutex
	var rw sync.RWMutex
	var wg sync.WaitGroup
	var once sync.Once
	r := 0
	for _, v := range []any{&mu, &rw, &wg, &once} {
		d := 0
		switch v.(type) {
		case *sync.Once:
			d = 1
		case *sync.WaitGroup:
			d = 2
		case *sync.RWMutex:
			d = 3
		case *sync.Mutex:
			d = 4
		}
		r = r*10 + d
	}
	return r // 4321
}

// R4
func syncEqual() int {
	var mu sync.Mutex
	var rw sync.RWMutex
	s := 0
	if any(&mu) == any(&rw) {
		s += 1
	}
	if any(&mu) == any(&mu) {
		s += 10
	}
	return s // 10
}

// R2
func syncPanic() int {
	var mu sync.Mutex
	var x any = &mu
	_ = x.(*sync.RWMutex)
	return 0
}

func main() {}
