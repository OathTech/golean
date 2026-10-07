package main

import "strings"

//go:noinline
func mkA(n int) string { return strings.Repeat("a", n) }

// conv is inlinable: at an inlined call the conversion's escape/mutation
// regime is the CALLER's; under -gcflags=-l it is a returned (escaping) slice.
func conv(s string) []byte { return []byte(s) }

func main() {
	s := mkA(5)
	b := conv(s)
	println("inline nomut 5", cap(b))
	b2 := conv(s)
	b2[0] = 'x'
	println("inline mut 5", cap(b2))
	t := mkA(100)
	b3 := conv(t)
	b3[0] = 'x'
	println("inline mut 100", cap(b3))
}
