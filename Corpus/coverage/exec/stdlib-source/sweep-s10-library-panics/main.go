package main

import (
	"bytes"
	"slices"
	"strings"
	"sync"
	"unsafe"
)

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: library panics reachable
// through the admitted stdlib that stdlib-source/* (strings.Repeat, Builder,
// bytes.Buffer, strconv, rand.Intn, bits.Div64) do not pin — bytes.Repeat and
// slices.Repeat with a negative count, slices.Delete out of range, an odd
// strings.NewReplacer argument list, sync.Once.Do(nil) (a nil func call inside
// Do), and unsafe.Slice with a nil pointer and a non-zero length (the runtime's
// own panic; expected to refuse at the frontend by name — a coverage gap).

func bytesRepeatNegative(z int) int {
	b := bytes.Repeat([]byte("a"), z)
	return len(b)
}

func slicesRepeatNegative(z int) int {
	s := slices.Repeat([]int{1}, z)
	return len(s)
}

func slicesDeleteOob(z int) int {
	s := []int{1, 2, 3}
	s = slices.Delete(s, 1, z)
	return len(s)
}

func newReplacerOdd() int {
	r := strings.NewReplacer("a")
	return len(r.Replace("abc"))
}

func onceDoNil() int {
	var o sync.Once
	o.Do(nil)
	return 0
}

func unsafeSliceNilLen(z int) int {
	var p *int
	s := unsafe.Slice(p, z)
	return len(s)
}

func main() {}
