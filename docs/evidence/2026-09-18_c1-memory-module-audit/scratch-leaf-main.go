package main

type Inner struct {
	arr [4]int8
	f   float64
	i   interface{}
	fn  func() int
	c   chan int
}
type Outer struct {
	inners [3]Inner
	tag    int
}

// width-narrowed int into a byte element of an array leaf
func narrowByte() int {
	var b [4]byte
	x := 300
	b[2] = byte(x)
	return int(b[2])
}

// int8 arithmetic overflow stored at a leaf
func narrowInt8() int {
	var o Outer
	var v int8 = 127
	v++
	o.inners[1].arr[3] = v
	return int(o.inners[1].arr[3])
}

// nested array-in-struct-in-array leaf write
func nestedLeaf() int {
	var arr [2]Outer
	arr[1].inners[2].arr[0] = 9
	arr[1].inners[2].f = 2.5
	arr[0].tag = 4
	return int(arr[1].inners[2].arr[0]) + arr[0].tag + int(arr[1].inners[2].f*2)
}

// nil into an interface slot in a struct field, then a non-nil
func nilIface() int {
	var o Outer
	o.inners[0].i = nil
	r := 0
	if o.inners[0].i == nil {
		r += 1
	}
	o.inners[0].i = 5
	if x, ok := o.inners[0].i.(int); ok {
		r += x
	}
	return r
}

// nil into a func-typed field, nil into a chan-typed field (the .chan nil canonical form)
func nilFuncChan() int {
	var o Outer
	o.inners[0].fn = nil
	o.inners[0].c = nil
	r := 0
	if o.inners[0].fn == nil {
		r += 1
	}
	if o.inners[0].c == nil {
		r += 2
	}
	o.inners[0].fn = func() int { return 4 }
	r += o.inners[0].fn()
	return r
}

// write through a slice header into an element past len but within cap, via reslice
func pastLenWithinCap() int {
	s := make([]int, 2, 5)
	t := s[:5]
	t[4] = 7
	u := s[:cap(s)]
	return u[4] + len(s)
}

// write at an out-of-range path → index panic; recovered
func outOfRange() (r int) {
	defer func() {
		if e := recover(); e != nil {
			r = 42
		}
	}()
	var a [3]int
	i := 3
	a[i] = 1
	return 0
}

// slice element that is a struct with an inner array: write through the slice
func sliceStructInnerArr() int {
	s := make([]Inner, 3)
	s[2].arr[1] = -5
	s[1].f = 1.5
	return int(s[2].arr[1]) + int(s[1].f*2)
}

// .defined type chain: named array of named array
type T1 [3]int
type T2 T1

func definedChain() int {
	var x T2
	x[1] = 5
	var y [2]T2
	y[1][2] = 6
	return x[1] + y[1][2]
}

// named interface variable, read-only (alloc at a defined interface type)
type Str interface{ Len() int }
type S3 struct{}

func (S3) Len() int { return 3 }
func namedIface() int {
	var s Str
	r := 0
	if s == nil {
		r += 1
	}
	s = S3{}
	r += s.Len()
	return r
}

// (d) len/cap of a pointer-to-array, nil and non-nil
func lenCapPtrArr() int {
	var p *[5]int
	q := &[7]int{}
	return len(p) + cap(p)*10 + len(q)*100 + cap(q)*1000
}

// a whole-struct store then a leaf write then a whole-struct read
func wholeThenLeaf() int {
	var o Outer
	o = Outer{tag: 1}
	o.inners[1].arr[0] = 2
	p := o
	return p.tag + int(p.inners[1].arr[0])
}

// pointer to a leaf inside a nested aggregate; write through the pointer
func ptrToLeaf() int {
	var o Outer
	p := &o.inners[2].arr[3]
	*p = 11
	q := &o.inners[2]
	q.arr[3]++
	return int(o.inners[2].arr[3])
}

func main() {
	println(narrowByte(), narrowInt8(), nestedLeaf(), nilIface(), nilFuncChan(), pastLenWithinCap(), outOfRange(), sliceStructInnerArr(), definedChain(), namedIface(), lenCapPtrArr(), wholeThenLeaf(), ptrToLeaf())
}
