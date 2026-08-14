// R1 probe: witness the implementation-chosen int/uint width.
package main

import (
	"strconv"
	"unsafe"
)

func main() {
	println("strconv.IntSize:", strconv.IntSize)
	println("unsafe.Sizeof(int(0)):", unsafe.Sizeof(int(0)))
	println("unsafe.Sizeof(uint(0)):", unsafe.Sizeof(uint(0)))
	println("unsafe.Sizeof(uintptr(0)):", unsafe.Sizeof(uintptr(0)))
	var x uint = ^uint(0)
	n := 0
	for x != 0 {
		x >>= 1
		n++
	}
	println("bits in ^uint(0):", n)
}
