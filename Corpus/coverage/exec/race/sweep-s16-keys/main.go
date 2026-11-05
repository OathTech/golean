package main

// S16 sweep, family KEYS (the defect-neighbourhood campaign, lane sweep/s16-race,
// 2026-10-27; matrix §A of the lane's report): two spellings of one cell, and the
// disjoint-path twins. Each subject is a two-goroutine program with one join
// channel; a racy subject's conflicting pair is HB-unordered on every schedule
// (lane racy: every enumerated path refuses, `go run -race` red), a race-free
// subject's readout is join-ordered (lane confluent: |set| = 1 certified).

type eKeys struct{ f, g int }

type oKeys struct {
	eKeys
	h int
}

type pairK struct{ a, b int }

type setterK interface{ SetB() }

func (p *pairK) SetB() { p.b = 1 }

// A4: a pointer to an array element beside the const-index read of it.
func keysPtrElemAlias() int {
	var a [2]int
	p := &a[1]
	done := make(chan int)
	go func() {
		*p = 1
		done <- 0
	}()
	y := a[1]
	<-done
	return y + a[1]
}

// A5: the same pointer write beside the OTHER element's read.
func keysPtrElemAliasDisjoint() int {
	var a [2]int
	p := &a[1]
	done := make(chan int)
	go func() {
		*p = 1
		done <- 0
	}()
	y := a[0]
	<-done
	return y*10 + a[1]
}

// A6: a slice of an array beside the array's element read.
func keysSliceOfArrayAlias() int {
	var a [2]int
	s := a[:]
	done := make(chan int)
	go func() {
		s[0] = 1
		done <- 0
	}()
	y := a[0]
	<-done
	return y + a[0]
}

// A7: a sub-slice with an offset: t[0] is s[1].
func keysSubsliceOffsetAlias() int {
	s := make([]int, 3)
	t := s[1:]
	done := make(chan int)
	go func() {
		t[0] = 1
		done <- 0
	}()
	y := s[1]
	<-done
	return y + s[1]
}

// A8: the same sub-slice write beside s[0].
func keysSubsliceOffsetDisjoint() int {
	s := make([]int, 3)
	t := s[1:]
	done := make(chan int)
	go func() {
		t[0] = 1
		done <- 0
	}()
	y := s[0]
	<-done
	return y*10 + s[1]
}

// A9: a pointer to a field beside the field's read.
func keysPtrFieldAlias() int {
	var o pairK
	pf := &o.a
	done := make(chan int)
	go func() {
		*pf = 1
		done <- 0
	}()
	y := o.a
	<-done
	return y + o.a
}

// A10: the same pointer write beside the sibling field's read.
func keysPtrFieldAliasDisjoint() int {
	var o pairK
	pf := &o.a
	done := make(chan int)
	go func() {
		*pf = 1
		done <- 0
	}()
	y := o.b
	<-done
	return y*10 + o.a
}

// A11: a promoted field written through the promotion, read through the
// explicit embedded path.
func keysPromotedFieldAlias() int {
	var o oKeys
	done := make(chan int)
	go func() {
		o.f = 1
		done <- 0
	}()
	y := o.eKeys.f
	<-done
	return y + o.eKeys.f
}

// A12: the promoted write beside the sibling promoted field's read.
func keysPromotedFieldDisjoint() int {
	var o oKeys
	done := make(chan int)
	go func() {
		o.f = 1
		done <- 0
	}()
	y := o.g
	<-done
	return y*10 + o.f
}

// A12: the promoted write beside the outer field's read.
func keysPromotedFieldOuterDisjoint() int {
	var o oKeys
	done := make(chan int)
	go func() {
		o.f = 1
		done <- 0
	}()
	y := o.h
	<-done
	return y*10 + o.f
}

// A13: a pointer-receiver method through an interface box writes o.b; main
// reads o.a — the dispatch reads the box, not the pointee.
func keysIfacePtrBoxPtrRecvDisjoint() int {
	var o pairK
	var i setterK = &o
	done := make(chan int)
	go func() {
		i.SetB()
		done <- 0
	}()
	y := o.a
	<-done
	return y*10 + o.b
}

// A14: the same dispatch beside the written field's read.
func keysIfacePtrBoxPtrRecvSame() int {
	var o pairK
	var i setterK = &o
	done := make(chan int)
	go func() {
		i.SetB()
		done <- 0
	}()
	y := o.b
	<-done
	return y + o.b
}

// A15: two pointers to one struct, disjoint fields.
func keysTwoPtrAliasesDisjoint() int {
	var o pairK
	p := &o
	q := &o
	done := make(chan int)
	go func() {
		p.a = 1
		done <- 0
	}()
	y := q.b
	<-done
	return y*10 + q.a
}

// A16: per-iteration loop variables captured by two goroutines writing
// disjoint elements.
func keysLoopvarPerIteration() int {
	var r [2]int
	done := make(chan int, 2)
	for i := 0; i < 2; i++ {
		go func() {
			r[i] = i + 1
			done <- 0
		}()
	}
	<-done
	<-done
	return r[0]*10 + r[1]
}

func gKeys0() int { return 3 }
func gKeys1() int { return 4 }

// A17: a function-valued variable read (called) beside its assignment.
func keysFuncValueVar() int {
	f := gKeys0
	done := make(chan int)
	go func() {
		f = gKeys1
		done <- 0
	}()
	y := f()
	<-done
	return y + f()
}

func main() {
	println(keysPtrElemAlias())
	println(keysPtrElemAliasDisjoint())
	println(keysSliceOfArrayAlias())
	println(keysSubsliceOffsetAlias())
	println(keysSubsliceOffsetDisjoint())
	println(keysPtrFieldAlias())
	println(keysPtrFieldAliasDisjoint())
	println(keysPromotedFieldAlias())
	println(keysPromotedFieldDisjoint())
	println(keysPromotedFieldOuterDisjoint())
	println(keysIfacePtrBoxPtrRecvDisjoint())
	println(keysIfacePtrBoxPtrRecvSame())
	println(keysTwoPtrAliasesDisjoint())
	println(keysLoopvarPerIteration())
	println(keysFuncValueVar())
}
