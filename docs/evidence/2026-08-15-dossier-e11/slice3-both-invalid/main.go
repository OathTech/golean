// E11 probe: three-index slice s[lo:hi:max] with hi > cap AND
// hi > max — which violation is reported?
package main

func main() {
	defer func() { println("recovered:", recover().(error).Error()) }()
	s := []int{0, 1, 2}
	lo, hi, max := 1, 5, 2
	_ = s[lo:hi:max]
}
