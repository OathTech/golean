// noodler probes — index and shift operands of every integer kind
// (spec#Index_expressions: "the index x must be of integer type or an
// untyped constant").
package main

func indexWithIntegerKinds() int {
	a := []int{10, 20, 30, 40}
	var i8 int8 = 1
	var u8 uint8 = 2
	var i64 int64 = 3
	var u uint = 0
	r := rune('b' - 'a')
	return a[i8] + a[u8] + a[i64] + a[u] + a[r]
}

func indexStringWithKinds() (byte, byte) {
	s := "hello"
	var u16 uint16 = 1
	var i32 int32 = 4
	return s[u16], s[i32]
}

func arrayIndexWithKinds() int {
	arr := [3]int{7, 8, 9}
	var u64 uint64 = 2
	var i16 int16 = 0
	return arr[u64]*10 + arr[i16]
}

func mapKeyKindsDistinct() (int, int) {
	m := map[any]int{}
	m[int8(1)] = 1
	m[int16(1)] = 2
	m[uint8(1)] = 3
	m[1] = 4
	return len(m), m[int16(1)]
}

func sliceBoundsWithKinds() int {
	a := []int{1, 2, 3, 4, 5}
	var lo uint8 = 1
	var hi int64 = 4
	var max uint16 = 5
	return len(a[lo:hi:max])*100 + cap(a[lo:hi:max])*10 + a[lo:hi][0]
}

func indexOutOfRangeUnsignedKind(n int) int {
	a := []int{1, 2}
	var u uint32 = uint32(n)
	return a[u]
}

func indexNegativeInt8Kind(n int) int {
	a := []int{1, 2}
	var i int8 = int8(n)
	return a[i]
}

func makeWithKinds() (int, int) {
	var n uint8 = 3
	var c int64 = 5
	s := make([]int, n, c)
	return len(s), cap(s)
}

func shiftCountsOfKinds() (int, uint8) {
	var a uint8 = 3
	var b int64 = 2
	var c uint = 1
	return 1<<a + 1<<b + 1<<c, 0xf0 >> a
}

func main() {}
