package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): nil-ness of a slice, map,
// func, channel and pointer through an interface box and BACK — the box of a
// typed nil is not nil (interfaces/typed-nil-* pin that), the value asserted
// back out of it is nil again, the comma-ok form likewise, and an EMPTY
// non-nil slice stays non-nil through the round trip (gc agrees; probed both
// sides first, .tmp/probes/nil-through-iface-assert).

func bit(b bool, w int) int {
	if b {
		return w
	}
	return 0
}

func nilThroughBox() int {
	var s []int
	var m map[int]int
	var f func()
	var c chan int
	var p *int
	bs, bm, bf, bc, bp := any(s), any(m), any(f), any(c), any(p)
	boxes := bit(bs == nil, 1) + bit(bm == nil, 2) + bit(bf == nil, 4) + bit(bc == nil, 8) + bit(bp == nil, 16)
	back := bit(bs.([]int) == nil, 1) + bit(bm.(map[int]int) == nil, 2) + bit(bf.(func()) == nil, 4) +
		bit(bc.(chan int) == nil, 8) + bit(bp.(*int) == nil, 16)
	s2, ok := bs.([]int)
	return boxes + back*100 + bit(s2 == nil, 10000) + bit(ok, 20000) + len(s2)*40000
}

func emptyThroughBox() int {
	e := any([]int{})
	return bit(e.([]int) == nil, 1) + bit(e == nil, 10) + bit(len(e.([]int)) == 0, 100)
}

func main() {
	println(nilThroughBox(), emptyThroughBox())
}
