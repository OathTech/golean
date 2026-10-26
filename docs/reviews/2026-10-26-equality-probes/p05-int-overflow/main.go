package main

func main() { run() }

func run() {
	var i8 int8 = 127
	i8++
	println(i8 == -128, i8 < 0)
	var u8 uint8 = 200
	u8 += 100
	println(u8 == 44, u8 < 200)
	var u64 uint64 = 1 << 63
	println(u64 > 1, u64 == 9223372036854775808, u64 > 1<<62, int64(u64) < 0, int64(u64) == -9223372036854775808)
	var i64 int64 = -9223372036854775808
	println(-i64 == i64, i64-1 == 9223372036854775807)
	var u32 uint32 = 0
	u32--
	println(u32 == 4294967295, u32 > 0, int32(u32) == -1)
	var i32 int32 = -1
	println(i32 < 1, uint32(i32) > 1, uint32(i32) == u32)
	x := 1 << 62
	println(x*4 == 0, x*2 < 0, x*2 == -9223372036854775808)
	var u uint = 0
	println(u-1 > 0, u-1 == 18446744073709551615)
	type MyInt int
	var m MyInt = 3
	println(m == 3, m < 4, MyInt(3) == m, int(m) == 3)
	var r rune = 'a'
	var b byte = 'a'
	println(r == 'a', b == 'a', r == rune(b), int32(r) == 97)
	// division and mod sign, then compare
	println(-7/2 == -3, -7%2 == -1, 7%-2 == 1)
	var mi int = -9223372036854775808
	println(mi/-1 == mi, mi%-1 == 0)
	// shifts
	var s uint8 = 1
	println(s<<8 == 0, s<<7 == 128, int8(s<<7) == -128)
	var sh uint = 70
	println(1<<sh == 0, int64(1)<<sh == 0, -1>>sh == -1)
}
