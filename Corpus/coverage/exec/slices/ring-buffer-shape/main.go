package main

// CL4 (window charter §4.4; docs/2026-10-03_window-corpus-disposition.md):
// the customer's `tracker.Inflights` ring buffer (raftsubject/tracker/
// inflights.go, bodies kept): a wrapping write cursor `(start+count) mod
// size`, growth by make+copy, inactive (stale) slots retained after
// FreeLE, the start reset on empty, and Clone (`append` onto nil) vs a
// struct copy whose slice header shares the backing. A miniature
// fixture is NOT a proof of Raft.

type inflight struct {
	index uint64
	bytes uint64
}

type inflights struct {
	start    int
	count    int
	bytes    uint64
	size     int
	maxBytes uint64
	buffer   []inflight
}

func (in *inflights) Clone() *inflights {
	ins := *in
	ins.buffer = append([]inflight(nil), in.buffer...)
	return &ins
}

func (in *inflights) Add(index, bytes uint64) {
	if in.Full() {
		panic("cannot add into a Full inflights")
	}
	next := in.start + in.count
	size := in.size
	if next >= size {
		next -= size
	}
	if next >= len(in.buffer) {
		in.grow()
	}
	in.buffer[next] = inflight{index: index, bytes: bytes}
	in.count++
	in.bytes += bytes
}

func (in *inflights) grow() {
	newSize := len(in.buffer) * 2
	if newSize == 0 {
		newSize = 1
	} else if newSize > in.size {
		newSize = in.size
	}
	newBuffer := make([]inflight, newSize)
	copy(newBuffer, in.buffer)
	in.buffer = newBuffer
}

func (in *inflights) FreeLE(to uint64) {
	if in.count == 0 || to < in.buffer[in.start].index {
		return
	}
	idx := in.start
	var i int
	var bytes uint64
	for i = 0; i < in.count; i++ {
		if to < in.buffer[idx].index {
			break
		}
		bytes += in.buffer[idx].bytes
		size := in.size
		if idx++; idx >= size {
			idx -= size
		}
	}
	in.count -= i
	in.bytes -= bytes
	in.start = idx
	if in.count == 0 {
		in.start = 0
	}
}

func (in *inflights) Full() bool {
	return in.count == in.size || (in.maxBytes != 0 && in.bytes >= in.maxBytes)
}

// Slot contents in buffer order, two decimal digits per slot.
func slots(in *inflights) uint64 {
	var s uint64
	for _, f := range in.buffer {
		s = s*100 + f.index
	}
	return s
}

// Add 1,2,3 (growth 0 → 1 → 2 → 4), free ≤ 2, add 4,5,6: the cursor
// wraps to slots 0 and 1, overwriting the stale entries.
func ringWrap() (uint64, int, int, int, bool, uint64) {
	in := &inflights{size: 4}
	for i := uint64(1); i <= 3; i++ {
		in.Add(i, 10*i)
	}
	in.FreeLE(2)
	for i := uint64(4); i <= 6; i++ {
		in.Add(i, 10*i)
	}
	return slots(in), in.start, in.count, len(in.buffer), in.Full(), in.bytes
}

// After FreeLE the freed slots keep their stale entries; freeing the
// rest resets start to 0 without clearing the buffer.
func ringStaleSlots() (uint64, int, int, uint64, int, int) {
	in := &inflights{size: 4}
	for i := uint64(1); i <= 3; i++ {
		in.Add(i, 1)
	}
	in.FreeLE(2)
	s1, st1, c1 := slots(in), in.start, in.count
	in.FreeLE(3)
	return s1, st1, c1, slots(in), in.start, in.count
}

// A struct copy shares the backing (header copy); Clone does not.
func ringCloneVsAlias() (uint64, uint64, uint64, int) {
	in := &inflights{size: 4}
	in.Add(1, 1)
	in.Add(2, 1)
	alias := *in
	clone := in.Clone()
	in.buffer[0].index = 9
	alias.Add(3, 1) // grows alias's own buffer: in is not affected
	return slots(in), slots(&alias), slots(clone), in.count
}

func main() {
	println(ringWrap())
	println(ringStaleSlots())
	println(ringCloneVsAlias())
}
