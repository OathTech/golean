package main

// println of every unsigned kind — gc's printuint (decimal), incl. uintptr
// (the machine's uint64, R1) and the uint64 maximum.
func printUints() int {
	var u8 uint8 = 255
	var u16 uint16 = 65535
	var u32 uint32 = 4294967295
	var u64 uint64 = 18446744073709551615
	var up uintptr = 12
	var u uint = 7
	println(u8, u16, u32, u64, up, u, byte(200))
	return 0
}
