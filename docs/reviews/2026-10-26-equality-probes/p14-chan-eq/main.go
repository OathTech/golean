package main

func main() { run() }

func run() {
	ch := make(chan int, 1)
	ch2 := make(chan int, 1)
	var rch <-chan int = ch
	var sch chan<- int = ch
	println(ch == ch, ch == ch2, ch != ch2, rch == ch, ch == rch, sch == ch, (<-chan int)(ch2) == rch)
	println(any(ch) == any(rch), any(ch) == any(ch), any(rch) == any((<-chan int)(ch)), any(ch) == any(ch2))
	var nc chan int
	println(nc == nil, ch == nil, nc == (chan int)(nil), nc != ch)
	var nr <-chan int
	println(nr == nil, nr == nc)
	m := map[chan int]int{}
	m[ch] = 1
	m[ch2] = 2
	m[ch] = 3
	println(len(m), m[ch], m[ch2], m[nc])
	mr := map[<-chan int]int{}
	mr[rch] = 1
	mr[ch] = 2
	println(len(mr), mr[rch])
	ma := map[any]int{}
	ma[ch] = 1
	ma[rch] = 2
	println(len(ma), ma[ch], ma[rch])
	switch rch {
	case ch:
		println("switch recv-only matched bidir")
	default:
		println("switch default")
	}
	type MyChan chan int
	mc := MyChan(ch)
	println(mc == ch, ch == mc, any(mc) == any(ch))
	arr := [2]chan int{ch, ch2}
	println(arr == [2]chan int{ch, ch2}, arr == [2]chan int{ch2, ch})
	type S struct{ C chan int }
	println(S{ch} == S{ch}, S{ch} == S{ch2})
}
