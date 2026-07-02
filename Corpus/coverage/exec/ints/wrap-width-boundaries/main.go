package main

func intWrapWidthBoundaries() int {
	score := 0

	var i16 int16 = -32768
	i16--
	if i16 == 32767 {
		score += 1
	}

	var i32 int32 = 2147483647
	i32++
	if i32 == -2147483648 {
		score += 10
	}

	var i64 int64 = 9223372036854775807
	i64++
	if i64 == -9223372036854775808 {
		score += 100
	}

	var u16 uint16 = 0
	u16--
	if u16 == 65535 {
		score += 1000
	}

	var u32 uint32 = 4294967295
	u32++
	if u32 == 0 {
		score += 10000
	}

	var u64 uint64 = 0
	u64--
	if u64 == 18446744073709551615 {
		score += 100000
	}

	return score
}

func main() {
	intWrapWidthBoundaries()
}
