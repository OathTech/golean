// R9 probe sheet: verbatim run-time panic messages and VALUE classes.
// Each case runs under its own recover; the tag line records
// box-class (runtime.Error / plain string / *runtime.PanicNilError)
// and the exact message.
package main

import "runtime"

func probe(name string, f func()) {
	defer func() {
		r := recover()
		if r == nil {
			println(name, "| no panic")
			return
		}
		switch v := r.(type) {
		case runtime.Error:
			println(name, "| runtime.Error |", v.Error())
		case string:
			println(name, "| plain string  |", v)
		case error:
			println(name, "| error         |", v.Error())
		default:
			println(name, "| other")
		}
	}()
	f()
}

func main() {
	xs := []int{0, 1, 2}
	i := 5
	probe("index-oob      ", func() { _ = xs[i] })
	lo, hi := 1, 9
	probe("slice-bounds   ", func() { _ = xs[lo:hi] })
	var m map[string]int
	probe("nil-map-write  ", func() { m["k"] = 1 })
	var p *int
	probe("nil-deref      ", func() { _ = *p })
	var x interface{} = 7
	probe("iface-conv     ", func() { _ = x.(string) })
	z := 0
	probe("div-zero       ", func() { _ = 1 / z })
	n := -1
	probe("make-chan-neg  ", func() { _ = make(chan int, n) })
	probe("make-slice-neg ", func() { _ = make([]int, n) })
	var nilch chan int
	probe("close-nil      ", func() { close(nilch) })
	ch := make(chan int)
	close(ch)
	probe("close-closed   ", func() { close(ch) })
	probe("send-closed    ", func() { ch <- 1 })
	probe("panic-nil      ", func() { panic(nil) })
	probe("sync-string-box", func() { panic("sync: negative WaitGroup counter") })
}
