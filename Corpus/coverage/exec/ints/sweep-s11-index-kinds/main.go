package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group N: an index of EVERY integer kind
// (spec#Index_expressions: any integer type, or an untyped constant representable by int) into a
// slice, an array and a string; slicing with two different index kinds; `make` sizes of every kind;
// array lengths from typed constants; `len`/`cap` as int in arithmetic; and the bounds panic text
// with an index of each kind not pinned by sweep-s10-bounds-kinds (uint8, uint64, int8 min, uint32,
// uintptr, rune, int16, a uint8 slice high). The index arrives as the entry argument where noted.

type dIdx uint8

func indexEveryKind() (int, int, int, int, int, int, int, int, int, int, int, int) {
	s := make([]int, 256)
	for i := range s {
		s[i] = i * 3
	}
	var a int8 = 127
	var b int16 = 200
	var c int32 = 3
	var d int64 = 255
	var e uint8 = 255
	var f uint16 = 1
	var g uint32 = 2
	var h uint64 = 254
	var i uint = 7
	var j uintptr = 9
	var k rune = 'a'
	var l dIdx = 100
	return s[a], s[b], s[c], s[d], s[e], s[f], s[g], s[h], s[i], s[j], s[k], s[l]
}

func indexStringAndArray() (byte, byte, int, int, byte, int) {
	str := "hello"
	var u8 uint8 = 4
	var d dIdx = 1
	arr := [8]int{1, 2, 3, 4, 5, 6, 7, 8}
	var i64 int64 = 7
	var u64 uint64 = 6
	return str[u8], str[d], arr[i64], arr[1.0], str[1<<1], arr[u64]
}

func sliceMixedKinds() (int, int, int, int) {
	s := []int{10, 20, 30, 40, 50, 60}
	var lo uint8 = 1
	var hi int64 = 4
	var mx uint16 = 5
	var lo2 uintptr = 2
	t := s[lo:hi]
	u := s[lo:hi:mx]
	v := s[lo2:]
	return len(t), cap(u), t[0], v[0]
}

func makeWithKinds() (int, int, int, int, int, int) {
	a := make([]int, uint8(3))
	b := make([]int, int64(2), uint16(5))
	var n uint32 = 4
	c := make([]byte, n)
	d := make(chan int, uint8(2))
	var p uintptr = 6
	e := make([]int, p)
	var r rune = 7
	f := make([]string, r)
	return len(a), cap(b), len(c), cap(d), len(e), len(f)
}

func arraySizesByKind() (int, int, int, int, int, int) {
	var a [uint8(3)]int
	var b [int64(2)]int
	var c [1 << 3]int
	var d [len([4]int{})]int
	const n = len(a)
	var e [uintptr(5)]byte
	return len(a), len(b), len(c), len(d), n, len(e)
}

func lenCapArithmetic() (int, int64, uint8, int) {
	s := make([]int, 3, 7)
	var i8 int8 = 2
	var u8 uint8 = 250
	return len(s) + int(i8), int64(cap(s)) * 1000000000000, u8 + uint8(len(s)), cap(s)<<1 - len(s)
}

func indexUint8PastLen(n int) int {
	s := []int{1, 2, 3}
	var i uint8 = uint8(n)
	return s[i]
}

func indexUint64Huge() int {
	s := []int{1, 2, 3}
	var i uint64 = 18446744073709551615
	return s[i]
}

func indexInt8Min(n int) int {
	s := []int{1, 2, 3}
	var i int8 = int8(n)
	return s[i]
}

func indexUint32Max() int {
	s := []int{1, 2, 3}
	var i uint32 = 4294967295
	return s[i]
}

func indexUintptrPastLen(n int) int {
	s := []int{1, 2, 3}
	var i uintptr = uintptr(n)
	return s[i]
}

func indexRuneNegative(n int) byte {
	s := "abc"
	var i rune = rune(n)
	return s[i]
}

func indexInt16MinArray(n int) int {
	arr := [4]int{1, 2, 3, 4}
	var i int16 = int16(n)
	return arr[i]
}

func sliceHighUint8PastCap(n int) int {
	s := make([]int, 2, 3)
	var h uint8 = uint8(n)
	return len(s[:h])
}

func main() {
	indexEveryKind()
	indexStringAndArray()
	sliceMixedKinds()
	makeWithKinds()
	arraySizesByKind()
	lenCapArithmetic()
	indexUint8PastLen(255)
	indexUint64Huge()
	indexInt8Min(-128)
	indexUint32Max()
	indexUintptrPastLen(5)
	indexRuneNegative(-1)
	indexInt16MinArray(-32768)
	sliceHighUint8PastCap(200)
}
