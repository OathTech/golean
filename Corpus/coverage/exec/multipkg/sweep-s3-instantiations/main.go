// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// K8 generic instantiations: identical arguments by different spellings are ONE type
// (Box[byte] ≡ Box[uint8], Box[any] ≡ Box[interface{}], Box[A] ≡ Box[int] for an alias A,
// Box[T] inside a generic at int ≡ Box[int], Box[func(x int)] ≡ Box[func(int)]); different
// arguments are different types, including two same-named packages' T.

import (
	bi "blue/inner"
	ri "red/inner"
)

type Box[T any] struct{ v T }
type Pair[A, B any] struct {
	a A
	b B
}
type A = int
type T struct{}

func mk[T any](x T) any { return Box[T]{x} }

// R1: fused spellings.
func instFused() int {
	s := 0
	if _, ok := any(Box[byte]{1}).(Box[uint8]); ok {
		s += 1
	}
	if _, ok := any(Box[any]{}).(Box[interface{}]); ok {
		s += 10
	}
	if _, ok := any(Box[A]{1}).(Box[int]); ok {
		s += 100
	}
	if _, ok := mk(1).(Box[int]); ok {
		s += 1000
	}
	if _, ok := any(Box[func(x int)]{}).(Box[func(int)]); ok {
		s += 10000
	}
	if _, ok := any(Box[[]byte]{}).(Box[[]uint8]); ok {
		s += 100000
	}
	if _, ok := any(Box[struct{}]{}).(Box[struct{}]); ok {
		s += 1000000
	}
	if _, ok := any(Pair[byte, A]{}).(Pair[uint8, int]); ok {
		s += 10000000
	}
	return s // 11111111
}

// R1: distinct arguments.
func instDistinct() int {
	s := 0
	if _, ok := any(Box[int]{}).(Box[int64]); ok {
		s += 1
	}
	if _, ok := any(Pair[int, string]{}).(Pair[string, int]); ok {
		s += 10
	}
	if _, ok := any(Box[*T]{}).(Box[T]); ok {
		s += 100
	}
	if _, ok := any(Box[[2]int]{}).(Box[[3]int]); ok {
		s += 1000
	}
	if _, ok := any(Box[func(...int)]{}).(Box[func([]int)]); ok {
		s += 10000
	}
	if _, ok := any(Box[ri.T]{}).(Box[bi.T]); ok {
		s += 100000
	}
	if _, ok := any(Box[Box[int]]{}).(Box[int]); ok {
		s += 1000000
	}
	if _, ok := any(Box[ri.T]{}).(Box[ri.T]); ok {
		s += 10000000
	}
	if _, ok := any(Box[Box[int]]{}).(Box[Box[int]]); ok {
		s += 100000000
	}
	return s // 110000000
}

// R3
func instSwitch() int {
	r := 0
	for _, v := range []any{Box[uint8]{}, Box[interface{}]{}, Box[int64]{}, Box[ri.T]{}, Box[bi.T]{}} {
		d := 0
		switch v.(type) {
		case Box[int]:
			d = 1
		case Box[byte]:
			d = 2
		case Box[any]:
			d = 3
		case Box[bi.T]:
			d = 4
		case Box[ri.T]:
			d = 5
		}
		r = r*10 + d
	}
	return r // 23054
}

// R4
func instEqual() int {
	s := 0
	if any(Box[byte]{1}) == any(Box[uint8]{1}) {
		s += 1
	}
	if any(Box[int]{1}) == any(Box[int64]{1}) {
		s += 10
	}
	if mk(1) == any(Box[int]{1}) {
		s += 100
	}
	if any(Box[ri.T]{}) == any(Box[bi.T]{}) {
		s += 1000
	}
	if any(Box[A]{1}) == any(Box[int]{1}) {
		s += 10000
	}
	return s // 10101
}

// R5
func instMapKeys() int {
	m := map[any]int{}
	m[Box[byte]{1}] = 1
	m[Box[uint8]{1}] = 2
	m[Box[int]{1}] = 3
	m[Box[any]{}] = 4
	m[Box[interface{}]{}] = 5
	m[Box[ri.T]{}] = 6
	m[Box[bi.T]{}] = 7
	m[Box[A]{1}] = 8
	return len(m)*10 + m[Box[uint8]{1}] // 52
}

// R6: the readout's Name() of each spelling.
func instReadoutByte() any   { return Box[byte]{1} }      // Box[uint8]
func instReadoutAny() any    { return Box[any]{} }        // Box[interface {}]
func instReadoutEmpty() any  { return Box[struct{}]{} }   // Box[struct {}]
func instReadoutPath() any   { return Box[ri.T]{} }       // Box[red/inner.T]
func instReadoutNested() any { return Box[Box[byte]]{} }  // Box[main.Box[uint8]]

// R2 for the spellings whose VALUES the observation seam refuses (a func / slice field):
// the instantiation's display in the panic text instead.
func instPanicFunc() int {
	var x any = Box[func(x int)]{}
	_ = x.(Box[int])
	return 0
}

func instPanicAlias() int {
	var x any = Pair[A, []byte]{}
	_ = x.(Box[int])
	return 0
}

// R2
func instPanicText() int {
	var x any = Box[byte]{1}
	return int(x.(Box[int]).v)
}

func instPanicPath() int {
	var x any = Box[ri.T]{}
	_ = x.(Box[bi.T])
	return 0
}

func main() {}
