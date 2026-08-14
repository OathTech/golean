// E11 probe: s[lo:hi] with BOTH indices invalid (lo > hi AND hi > cap)
// — which check fires first? The machine checks HIGH then LOW.
package main

func main() {
	defer func() { println("recovered:", recover().(error).Error()) }()
	s := []int{0, 1, 2}
	lo, hi := 5, 4
	_ = s[lo:hi]
}
