package main

// stdlib slice 3 (2026-09-04): println of every signed integer kind — gc's
// printint (decimal, `-` for negatives), a defined type printing as its
// underlying kind, and the int64 extremes.
type Code int

func printInts() int {
	println(0, 1, -1, 42, -7, 9223372036854775807, -9223372036854775808)
	var i8 int8 = -128
	var i16 int16 = 32767
	var i32 int32 = -5
	var i64 int64 = 1 << 62
	println(i8, i16, i32, i64, Code(7), Code(-7))
	return 0
}
