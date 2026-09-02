package main

// Detector-soundness probes, FOOTPRINT hunt: each subject targets one
// `stepAccesses` arm or one recorded approximation (Race.lean's inventory)
// with a shape the corpus does not already pin, looking for the third cell
// (gc -race red, machine DRF). Expected cells are stated per subject.

type fpS struct{ a, b int }

type fpArr struct {
	arr [2]int
	n   int
}

type fpPt struct{ x int }

func (p fpPt) Val() int { return p.x }

var fpGlobal int

// F-1: whole-struct COPY beside a disjoint field write — the copy reads every
// field. Expect agree-race.
func fpStructCopyVsFieldWrite() int {
	var s fpS
	done := make(chan int)
	go func() {
		s.b = 1
		done <- 0
	}()
	t := s
	<-done
	return t.a
}

// F-2: interface BOXING of a struct value beside a field write. Expect
// agree-race.
func fpIfaceBoxVsFieldWrite() int {
	var s fpS
	done := make(chan int)
	go func() {
		s.b = 1
		done <- 0
	}()
	var i interface{} = s
	<-done
	return i.(fpS).a
}

// F-3: channel SEND of a struct value (the operand copy) beside a field write.
// Expect agree-race.
func fpSendStructVsFieldWrite() int {
	var s fpS
	ch := make(chan fpS, 1)
	done := make(chan int)
	go func() {
		s.b = 1
		done <- 0
	}()
	ch <- s
	<-done
	v := <-ch
	return v.a
}

// F-4: DEFER argument evaluation reads x at the defer statement, before the
// join. Expect agree-race.
func fpDeferArgVsWrite() int {
	x := 0
	r := 0
	done := make(chan int)
	go func() {
		x = 1
		done <- 0
	}()
	func() {
		defer func(v int) { r = v }(x)
		<-done
	}()
	return r
}

// F-5: METHOD VALUE with a value receiver copies the receiver at creation
// (spec §Method values: "the receiver is evaluated and saved"). Expect
// agree-race (a machine that binds lazily would read at the call, after the
// join — a DRF verdict here is a HOLE).
func fpMethodValueCopyVsWrite() int {
	var p fpPt
	done := make(chan int)
	go func() {
		p.x = 1
		done <- 0
	}()
	f := p.Val
	<-done
	return f()
}

// F-6: tuple-assignment swap reads b while the child writes b. Expect
// agree-race.
func fpSwapVsWrite() int {
	a, b := 1, 2
	done := make(chan int)
	go func() {
		b = 5
		done <- 0
	}()
	a, b = b, a
	<-done
	return a + b
}

// F-7 CONTROL: copy() reads the source elements (footprint copySlice) beside a
// source element write. Expect agree-race.
func fpCopySrcVsWrite() int {
	src := []int{1, 2}
	dst := make([]int, 2)
	done := make(chan int)
	go func() {
		src[0] = 9
		done <- 0
	}()
	copy(dst, src)
	<-done
	return dst[1]
}

// F-8: append IN PLACE writes backing[len] in the child; main reads that cell
// through a reslice. Expect agree-race.
func fpAppendInPlaceVsReslice() int {
	s := make([]int, 1, 4)
	done := make(chan int)
	go func() {
		s2 := append(s, 5)
		done <- len(s2)
	}()
	t := s[:2]
	r := t[1]
	<-done
	return r
}

// F-9: slicing an array LOCAL `a[:]` takes its address (gc reads no
// elements), then a disjoint-element read. Expect agree-DRF (over-refusal
// here means the slice op evaluated `a` by value).
func fpSliceOfArrayVsElemWrite() int {
	var a [3]int
	done := make(chan int)
	go func() {
		a[0] = 4
		done <- 0
	}()
	sl := a[:]
	r := sl[2]
	<-done
	return r
}

// F-10 CONTROL: pointer-to-array element read p[1] beside a[0] write (the
// triage-L5 `.addr` indexGet arm). Expect agree-DRF.
func fpPtrArrayElemVsWrite() int {
	var a [2]int
	p := &a
	done := make(chan int)
	go func() {
		a[0] = 4
		done <- 0
	}()
	r := p[1]
	<-done
	return r
}

// F-11: DYNAMIC-index value-path array read `a[i]` beside a disjoint element
// write (called with i = 1). gc DRF; the machine reads the whole cell — O1's
// dynamic-index RESIDUAL under the Q-RACEPATH ruling. Expect over-refusal,
// by design and recorded.
func fpArrayDynIndexVsWrite(i int) int {
	var a [2]int
	done := make(chan int)
	go func() {
		a[0] = 4
		done <- 0
	}()
	r := a[i]
	<-done
	return r
}

// F-12: constant index THEN field: a[1].x read beside a[0].x write — the
// Q-RACEPATH narrowing's indexGet→fieldGet chain form. gc DRF; machine DRF
// only with the constant-index narrowing.
func fpArrayConstIndexFieldVsWrite() int {
	var a [2]fpPt
	done := make(chan int)
	go func() {
		a[0].x = 4
		done <- 0
	}()
	r := a[1].x
	<-done
	return r
}

// F-13: field THEN constant index: s.arr[1] read beside s.arr[0] write
// (fieldGet→indexGet chain). gc DRF; machine DRF only with the narrowing.
func fpFieldArrayConstIndexVsWrite() int {
	var s fpArr
	done := make(chan int)
	go func() {
		s.arr[0] = 4
		done <- 0
	}()
	r := s.arr[1]
	<-done
	return r
}

// F-14: constant-index read beside the SAME element's write — the narrowing
// must not hide the race. Expect agree-race.
func fpArrayConstIndexSameElem() int {
	var a [2]int
	done := make(chan int)
	go func() {
		a[1] = 4
		done <- 0
	}()
	r := a[1]
	<-done
	return r
}

// F-15: constant-index read beside a WHOLE-array write (prefix overlap).
// Expect agree-race.
func fpArrayConstIndexVsWholeWrite() int {
	var a [2]int
	done := make(chan int)
	go func() {
		a = [2]int{7, 8}
		done <- 0
	}()
	r := a[1]
	<-done
	return r
}

// F-16: range over a SLICE reading elements 0..1 while the child writes
// element 2 of the shared backing. Expect agree-DRF.
func fpRangeSliceDisjointVsWrite() int {
	s := make([]int, 3)
	head := s[:2]
	done := make(chan int)
	go func() {
		s[2] = 9
		done <- 0
	}()
	r := 0
	for _, v := range head {
		r += v
	}
	<-done
	return r
}

// F-17: range over an ARRAY value copies the array at range start (gc reads
// every element) beside an element write. Expect agree-race.
func fpRangeArrayVsElemWrite() int {
	var a [2]int
	done := make(chan int)
	go func() {
		a[1] = 9
		done <- 0
	}()
	r := 0
	for _, v := range a {
		r += v
	}
	<-done
	return r
}

// F-18: a SELECT send clause evaluates its value operand (the read of x)
// beside the child's write. Expect agree-race.
func fpSelectSendValueVsWrite() int {
	x := 0
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		x = 1
		done <- 0
	}()
	select {
	case ch <- x:
	default:
	}
	<-done
	return <-ch
}

// F-19: RECEIVE INTO A SHARED VARIABLE — the receive statement's target store
// (`enterRecvTargets` → storeK) beside the child's write of x. Expect
// agree-race (a DRF verdict would mean the registry op's store bypasses the
// footprint).
func fpRecvIntoSharedVsWrite() int {
	x := 0
	ch := make(chan int, 1)
	ch <- 3
	done := make(chan int)
	go func() {
		x = 1
		done <- 0
	}()
	x = <-ch
	<-done
	return x
}

// F-20: the PARKED receiver variant: main parks on `x = <-ch`, the child
// sends then writes x — the woken receiver's target store is unordered with
// the child's post-send write. Expect agree-race.
func fpWokenRecvIntoSharedVsWrite() int {
	x := 0
	ch := make(chan int)
	done := make(chan int)
	go func() {
		ch <- 3
		x = 1
		done <- 0
	}()
	x = <-ch
	<-done
	return x
}

// F-21 CONTROL: package-level variable written by the child, read by main
// with no edge. Expect agree-race.
func fpGlobalVsWrite() int {
	fpGlobal = 0
	done := make(chan int)
	go func() {
		fpGlobal = 1
		done <- 0
	}()
	r := fpGlobal
	<-done
	return r
}

// F-22 CONTROL: closure-captured local written by the child, read by main
// with no edge. Expect agree-race.
func fpCapturedVsWrite() int {
	x := 0
	done := make(chan int)
	go func() {
		x = 1
		done <- 0
	}()
	r := x
	<-done
	return r
}

// F-23 CONTROL: map read beside a DISJOINT-key write (a map object is one
// location). Expect agree-race.
func fpMapDisjointKeys() int {
	m := map[int]int{1: 1}
	done := make(chan int)
	go func() {
		m[2] = 2
		done <- 0
	}()
	r := m[1]
	<-done
	return r
}

// F-24: []byte(s) reads the string variable beside the child's write. Expect
// agree-race.
func fpBytesFromStringVsWrite() int {
	s := "ab"
	done := make(chan int)
	go func() {
		s = "c"
		done <- 0
	}()
	b := []byte(s)
	<-done
	return len(b)
}

// F-25 CONTROL: the spawn ARGUMENT is evaluated in the parent before the go
// statement (spec §Go statements), so the child's later write is spawn-edge
// ordered after it. Expect agree-DRF.
func fpSpawnArgVsChildWrite() int {
	x := 5
	done := make(chan int)
	go func(v int) {
		x = v + 1
		done <- 0
	}(x)
	<-done
	return x
}

// F-26: nested struct field path read s.in.a beside a write of s.in.b —
// disjoint leaf paths under one root (fieldGet chain, two hops). Expect
// agree-DRF.
type fpIn struct{ a, b int }
type fpOut struct {
	in fpIn
	n  int
}

func fpNestedFieldDisjoint() int {
	var s fpOut
	done := make(chan int)
	go func() {
		s.in.b = 1
		done <- 0
	}()
	r := s.in.a
	<-done
	return r
}

// F-27: WHOLE inner-struct read s.in beside a write of s.in.b — the read's
// narrowed path (s.in) is a prefix of the write's. Expect agree-race.
func fpNestedWholeVsField() int {
	var s fpOut
	done := make(chan int)
	go func() {
		s.in.b = 1
		done <- 0
	}()
	t := s.in
	<-done
	return t.a
}

func main() {
	println(fpStructCopyVsFieldWrite(), fpIfaceBoxVsFieldWrite(), fpSendStructVsFieldWrite(),
		fpDeferArgVsWrite(), fpMethodValueCopyVsWrite(), fpSwapVsWrite(), fpCopySrcVsWrite(),
		fpAppendInPlaceVsReslice(), fpSliceOfArrayVsElemWrite(), fpPtrArrayElemVsWrite(),
		fpArrayDynIndexVsWrite(1), fpArrayConstIndexFieldVsWrite(), fpFieldArrayConstIndexVsWrite(),
		fpArrayConstIndexSameElem(), fpArrayConstIndexVsWholeWrite(), fpRangeSliceDisjointVsWrite(),
		fpRangeArrayVsElemWrite(), fpSelectSendValueVsWrite(), fpRecvIntoSharedVsWrite(),
		fpWokenRecvIntoSharedVsWrite(), fpGlobalVsWrite(), fpCapturedVsWrite(), fpMapDisjointKeys(),
		fpBytesFromStringVsWrite(), fpSpawnArgVsChildWrite(), fpNestedFieldDisjoint(), fpNestedWholeVsField())
}
