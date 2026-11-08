package main

import "slices"

// S16 sweep, family FOOTPRINT (the defect-neighbourhood campaign, lane
// sweep/s16-race, 2026-10-27; matrix §A19–A20, §B, §C, §D, §E30–E31): what each
// emitting operation and each multi-cell apply arm records, beside a concurrent
// access that gc's -race build does or does not see. Six subjects are RED PINS
// (strict rows, expected gc ok, the machine refuses `race`): the BUG-041 field-chain
// instance, the BUG-132 length-1 window, `clear(s)` (BUG-370: gc's memclr is not
// instrumented, go_mem calls it a race) and the three zero-size cells (BUG-371).

type arrHolder struct {
	arr   [2]int
	other int
}

type sliceHolder struct {
	s []int
	t int
}

type zeroHolder struct {
	n int
	z struct{}
}

type pairF struct{ a, b int }

func (p pairF) get() int { return p.a + p.b }
func (p *pairF) set()    { p.a = 1 }

// A19: a value-receiver method called through a pointer copies the whole
// pointee (gc copies *p), beside a field write.
func footprintValueRecvViaPtrWholeRead() int {
	o := pairF{}
	p := &o
	done := make(chan int)
	go func() {
		o.b = 1
		done <- 0
	}()
	y := p.get()
	<-done
	return y + o.b
}

// A20: a pointer-receiver method on an addressable value takes &o (no read
// of o) and writes o.a, beside a write of o.b.
func footprintPtrRecvOnValueNoRead() int {
	o := pairF{}
	done := make(chan int)
	go func() {
		o.b = 1
		done <- 0
	}()
	o.set()
	<-done
	return o.a*10 + o.b
}

// B3: two dynamic-index WRITES to distinct array elements (address path).
func footprintArrayDynIndexWriteWriteDisjoint(i int, j int) int {
	var a [2]int
	done := make(chan int)
	go func() {
		a[i] = 1
		done <- 0
	}()
	a[j] = 2
	<-done
	return a[0]*10 + a[1]
}

// B4: a dynamic-index read through a pointer to an array beside the other
// element's write.
func footprintPtrArrayDynIndexRead(i int) int {
	var a [2]int
	p := &a
	done := make(chan int)
	go func() {
		a[0] = 1
		done <- 0
	}()
	y := p[i]
	<-done
	return y*10 + a[0]
}

// B5: a dynamic-index read of an array FIELD beside a sibling field's write.
func footprintStructArrayFieldDynSibling(i int) int {
	var o arrHolder
	done := make(chan int)
	go func() {
		o.other = 1
		done <- 0
	}()
	y := o.arr[i]
	<-done
	return y*10 + o.other
}

// B6: a dynamic-index read of an array field beside the other element's
// write (BUG-041's class under a field chain).
func footprintStructArrayFieldDynOtherElem(i int) int {
	var o arrHolder
	done := make(chan int)
	go func() {
		o.arr[0] = 1
		done <- 0
	}()
	y := o.arr[i]
	<-done
	return y*10 + o.arr[0]
}

// B7: a dynamic-index slice read beside the other element's write.
func footprintSliceDynIndexDisjoint(i int) int {
	s := make([]int, 2)
	done := make(chan int)
	go func() {
		s[0] = 1
		done <- 0
	}()
	y := s[i]
	<-done
	return y*10 + s[0]
}

// B9: a slice field's element read beside the other element's write.
func footprintStructSliceFieldElemDisjoint(i int) int {
	o := sliceHolder{s: make([]int, 2)}
	done := make(chan int)
	go func() {
		o.s[0] = 1
		done <- 0
	}()
	y := o.s[i]
	<-done
	return y*10 + o.s[0]
}

// B9: a slice field's element read beside the sibling field's write.
func footprintStructSliceFieldSibling(i int) int {
	o := sliceHolder{s: make([]int, 2)}
	done := make(chan int)
	go func() {
		o.t = 1
		done <- 0
	}()
	y := o.s[i]
	<-done
	return y*10 + o.t
}

// B10: a slice of slices, disjoint inner backings.
func footprintSliceOfSlicesDisjoint() int {
	ss := [][]int{make([]int, 1), make([]int, 1)}
	done := make(chan int)
	go func() {
		ss[1][0] = 1
		done <- 0
	}()
	y := ss[0][0]
	<-done
	return y*10 + ss[1][0]
}

// B11: len(s) reads the header beside an element write.
func footprintSliceLenVsElemWrite() int {
	s := make([]int, 2)
	done := make(chan int)
	go func() {
		s[0] = 1
		done <- 0
	}()
	y := len(s)
	<-done
	return y*10 + s[0]
}

// B12: a reslice writes the header variable beside an element read through
// the same variable.
func footprintResliceVsElemRead() int {
	s := []int{1, 2}
	done := make(chan int)
	go func() {
		s = s[1:]
		done <- 0
	}()
	y := s[0]
	<-done
	return y + s[0]
}

// B13: `s == nil` reads the header beside an element write.
func footprintSliceNilCompareVsElemWrite() int {
	s := make([]int, 1)
	done := make(chan int)
	go func() {
		s[0] = 1
		done <- 0
	}()
	y := 0
	if s == nil {
		y = 5
	}
	<-done
	return y*10 + s[0]
}

// B13: `m == nil` reads the map variable beside a map write (the payload).
func footprintMapNilCompareVsWrite() int {
	m := map[int]int{}
	done := make(chan int)
	go func() {
		m[1] = 2
		done <- 0
	}()
	y := 0
	if m == nil {
		y = 5
	}
	<-done
	return y*10 + len(m)
}

// B13: `ch == nil` reads the channel variable beside a close.
func footprintChanNilCompareVsClose() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		close(ch)
		done <- 0
	}()
	y := 0
	if ch == nil {
		y = 5
	}
	<-done
	_, ok := <-ch
	if !ok {
		y = y + 7
	}
	return y
}

// B14: an array value copy reads every element, beside an element write.
func footprintArrayCopyVsElemWrite() int {
	var a [2]int
	done := make(chan int)
	go func() {
		a[1] = 1
		done <- 0
	}()
	b := a
	y := b[0]
	<-done
	return y + a[1]
}

// B16: a string index reads the string variable beside its assignment.
func footprintStringIndexVsAssign() int {
	s := "ab"
	done := make(chan int)
	go func() {
		s = "cd"
		done <- 0
	}()
	y := int(s[0])
	<-done
	return y + len(s)
}

// B16: two readers of one string.
func footprintStringTwoReaders() int {
	s := "ab"
	r1 := 0
	done := make(chan int)
	go func() {
		r1 = int(s[1])
		done <- 0
	}()
	r0 := int(s[0])
	<-done
	return r0 + r1
}

// B16: range over a string reads the variable beside its assignment.
func footprintRangeStringVsAssign() int {
	s := "ab"
	done := make(chan int)
	go func() {
		s = "cd"
		done <- 0
	}()
	n := 0
	for range s {
		n++
	}
	<-done
	return n + len(s)
}

// B20: two map writes at different keys (one location).
func footprintMapWriteWrite() int {
	m := map[int]int{}
	done := make(chan int)
	go func() {
		m[1] = 1
		done <- 0
	}()
	m[2] = 2
	<-done
	return len(m)
}

// B21: delete beside a read of another key.
func footprintMapDeleteVsRead() int {
	m := map[int]int{1: 1, 2: 2}
	done := make(chan int)
	go func() {
		delete(m, 1)
		done <- 0
	}()
	y := m[2]
	<-done
	return y*10 + len(m)
}

// B21: delete of an ABSENT key beside a read (gc's mapdelete writes
// unconditionally).
func footprintMapDeleteAbsentVsRead() int {
	m := map[int]int{1: 1, 2: 2}
	done := make(chan int)
	go func() {
		delete(m, 9)
		done <- 0
	}()
	y := m[2]
	<-done
	return y*10 + len(m)
}

// B22: clear(m) beside a read.
func footprintMapClearVsRead() int {
	m := map[int]int{1: 1, 2: 2}
	done := make(chan int)
	go func() {
		clear(m)
		done <- 0
	}()
	y := m[2]
	<-done
	return y*10 + len(m)
}

// B23: two map readers.
func footprintMapTwoReaders() int {
	m := map[int]int{1: 1, 2: 2}
	r1 := 0
	done := make(chan int)
	go func() {
		r1 = m[1]
		done <- 0
	}()
	r0 := m[2]
	<-done
	return r0*10 + r1
}

// B23: two map rangers.
func footprintMapTwoRangers() int {
	m := map[int]int{1: 1, 2: 2}
	r1 := 0
	done := make(chan int)
	go func() {
		for _, v := range m {
			r1 += v
		}
		done <- 0
	}()
	r0 := 0
	for _, v := range m {
		r0 += v
	}
	<-done
	return r0*10 + r1
}

// C2: sorting an UNSORTED window beside a read of an element gc moves.
func footprintSortUnsortedVsRead() int {
	s := []int{3, 2, 1}
	done := make(chan int)
	go func() {
		slices.Sort(s)
		done <- 0
	}()
	y := s[0]
	<-done
	return y + s[0]
}

// C3: sorting s[:2] beside a write of s[2], outside the window.
func footprintSortWindowVsOutsideWrite() int {
	s := []int{2, 1, 0}
	done := make(chan int)
	go func() {
		slices.Sort(s[:2])
		done <- 0
	}()
	s[2] = 9
	<-done
	return s[0]*100 + s[1]*10 + s[2]
}

// C4: sorting a LENGTH-1 window (gc's insertion sort performs no access)
// beside a write of its element.
func footprintSortLen1VsWrite() int {
	s := []int{1}
	done := make(chan int)
	go func() {
		slices.Sort(s)
		done <- 0
	}()
	s[0] = 2
	<-done
	return s[0]
}

// C5: sorting beside a write inside the window.
func footprintSortVsInsideWrite() int {
	s := []int{2, 1}
	done := make(chan int)
	go func() {
		slices.Sort(s)
		done <- 0
	}()
	s[0] = 9
	<-done
	return s[0] + s[1]
}

// C6: the sort, then the join, then the read.
func footprintSortThenEdgeRead() int {
	s := []int{3, 1, 2}
	done := make(chan int)
	go func() {
		slices.Sort(s)
		done <- 0
	}()
	<-done
	return s[0]*100 + s[1]*10 + s[2]
}

// C8: copy's destination writes beside a read of the destination.
func footprintCopyDstVsRead() int {
	dst := make([]int, 2)
	src := []int{1, 2}
	done := make(chan int)
	go func() {
		copy(dst, src)
		done <- 0
	}()
	y := dst[0]
	<-done
	return y + dst[0]
}

// C9: copy with count 0 touches no element.
func footprintCopyCountZero() int {
	dst := make([]int, 2)
	src := []int{1, 2}
	done := make(chan int)
	go func() {
		copy(dst[:0], src)
		done <- 0
	}()
	dst[0] = 5
	src[0] = 6
	<-done
	return dst[0]*10 + src[0]
}

// C10: copy between disjoint runs of one backing beside a third element's
// write.
func footprintCopyDisjointRuns() int {
	s := make([]int, 3)
	done := make(chan int)
	go func() {
		copy(s[0:1], s[2:3])
		done <- 0
	}()
	s[1] = 5
	<-done
	return s[0]*100 + s[1]*10 + s[2]
}

// C11: clear(s) beside an element read.
func footprintClearSliceVsRead() int {
	s := []int{1, 2}
	done := make(chan int)
	go func() {
		clear(s)
		done <- 0
	}()
	y := s[0]
	<-done
	return y + s[1]
}

// C12: clear of an empty window beside an element write.
func footprintClearEmptySlice() int {
	s := []int{1, 2}
	done := make(chan int)
	go func() {
		clear(s[:0])
		done <- 0
	}()
	s[0] = 5
	<-done
	return s[0]*10 + s[1]
}

// C13: an in-place append writes the backing's tail beside a read through
// a longer alias of the same backing.
func footprintAppendInplaceTailVsRead() int {
	s := make([]int, 1, 2)
	t := s[:2]
	done := make(chan int)
	go func() {
		s = append(s, 7)
		done <- 0
	}()
	y := t[1]
	<-done
	return y + len(s)
}

// C14: a spilling append reads the old backing (gc's growslice reads the
// old elements) beside a write through an alias of the old backing.
func footprintAppendSpillReadsOld() int {
	s := make([]int, 2, 2)
	t := s
	done := make(chan int)
	go func() {
		t[0] = 5
		done <- 0
	}()
	s = append(s, 1)
	<-done
	return len(s)*10 + t[0]
}

// C15: append(s, u...) reads u's elements beside a write of u[0].
func footprintAppendFromSliceReadsSrc() int {
	u := []int{1, 2}
	s := make([]int, 0, 4)
	done := make(chan int)
	go func() {
		u[0] = 3
		done <- 0
	}()
	s = append(s, u...)
	<-done
	return len(s)*10 + u[0]
}

// C16: the spilled backing is fresh: a post-spill write to s[0] beside an
// HB-ordered write to the old backing's element.
func footprintAppendSpillFreshBacking() int {
	s := make([]int, 1, 1)
	old := s
	s = append(s, 2)
	done := make(chan int)
	go func() {
		old[0] = 5
		done <- 0
	}()
	s[0] = 9
	<-done
	return s[0]*10 + old[0]
}

// D1: two writes of a zero-size variable.
func footprintZeroSizeWriteWrite() int {
	var z struct{}
	done := make(chan int)
	go func() {
		z = struct{}{}
		done <- 0
	}()
	z = struct{}{}
	<-done
	_ = z
	return 1
}

// D2: a read of a zero-size variable beside its write.
func footprintZeroSizeReadWrite() int {
	var z struct{}
	done := make(chan int)
	go func() {
		z = struct{}{}
		done <- 0
	}()
	w := z
	<-done
	_ = w
	return 1
}

// D3: two writes of a zero-length array.
func footprintZeroArrayWriteWrite() int {
	var a [0]int
	done := make(chan int)
	go func() {
		a = [0]int{}
		done <- 0
	}()
	a = [0]int{}
	<-done
	return len(a) + 1
}

// D6: a zero-size FIELD inside a sized struct, written beside a whole-struct
// read of the holder (gc instruments the sized read only; the zero-size store
// is a no-op without a race call).
func footprintZeroSizeFieldVsWholeRead() int {
	var o zeroHolder
	done := make(chan int)
	go func() {
		o.z = struct{}{}
		done <- 0
	}()
	w := o
	<-done
	return w.n + 1
}

// D4/D5: the right operand of && is read only when the left is true.
func footprintShortCircuit(a int) int {
	shared := 0
	done := make(chan int)
	go func() {
		shared = 1
		done <- 0
	}()
	y := 0
	if a == 1 && shared == 1 {
		y = 1
	}
	<-done
	return y*10 + shared
}

// E30: a write in a deferred closure beside the parent's read.
func footprintDeferredWriteVsRead() int {
	x := 0
	done := make(chan int)
	go func() {
		defer func() {
			x = 1
			done <- 0
		}()
	}()
	y := x
	<-done
	return y + x
}

// E31: a write after recover beside the parent's read.
func footprintRecoverThenWriteVsRead() int {
	x := 0
	done := make(chan int)
	go func() {
		defer func() {
			recover()
			x = 1
			done <- 0
		}()
		panic("p")
	}()
	y := x
	<-done
	return y + x
}

func main() {
	println(footprintValueRecvViaPtrWholeRead())
	println(footprintPtrRecvOnValueNoRead())
	println(footprintArrayDynIndexWriteWriteDisjoint(0, 1))
	println(footprintPtrArrayDynIndexRead(1))
	println(footprintStructArrayFieldDynSibling(1))
	println(footprintStructArrayFieldDynOtherElem(1))
	println(footprintSliceDynIndexDisjoint(1))
	println(footprintStructSliceFieldElemDisjoint(1))
	println(footprintStructSliceFieldSibling(1))
	println(footprintSliceOfSlicesDisjoint())
	println(footprintSliceLenVsElemWrite())
	println(footprintResliceVsElemRead())
	println(footprintSliceNilCompareVsElemWrite())
	println(footprintMapNilCompareVsWrite())
	println(footprintChanNilCompareVsClose())
	println(footprintArrayCopyVsElemWrite())
	println(footprintStringIndexVsAssign())
	println(footprintStringTwoReaders())
	println(footprintRangeStringVsAssign())
	println(footprintMapWriteWrite())
	println(footprintMapDeleteVsRead())
	println(footprintMapDeleteAbsentVsRead())
	println(footprintMapClearVsRead())
	println(footprintMapTwoReaders())
	println(footprintMapTwoRangers())
	println(footprintSortUnsortedVsRead())
	println(footprintSortWindowVsOutsideWrite())
	println(footprintSortLen1VsWrite())
	println(footprintSortVsInsideWrite())
	println(footprintSortThenEdgeRead())
	println(footprintCopyDstVsRead())
	println(footprintCopyCountZero())
	println(footprintCopyDisjointRuns())
	println(footprintClearSliceVsRead())
	println(footprintClearEmptySlice())
	println(footprintAppendInplaceTailVsRead())
	println(footprintAppendSpillReadsOld())
	println(footprintAppendFromSliceReadsSrc())
	println(footprintAppendSpillFreshBacking())
	println(footprintZeroSizeWriteWrite())
	println(footprintZeroSizeReadWrite())
	println(footprintZeroArrayWriteWrite())
	println(footprintZeroSizeFieldVsWholeRead())
	println(footprintShortCircuit(0))
	println(footprintShortCircuit(1))
	println(footprintDeferredWriteVsRead())
	println(footprintRecoverThenWriteVsRead())
}
