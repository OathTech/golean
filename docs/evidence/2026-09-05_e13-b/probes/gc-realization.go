package main

import "fmt"

var w int

func wit(x int) int { w = w*31 + x; return x }
func sink(a, b int) int { return a + b }

type T struct{ x int }

func (t *T) M() int { w = w*31 + 7; return 7 }

func run(name string, f func() int) {
	w = 0
	defer func() { fmt.Printf("%s|%v|w=%d\n", name, recover(), w) }()
	r := f()
	fmt.Printf("%s|value=%d|", name, r)
}

func main() {
	var iv interface{} = "s"
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	var p *int
	z := 0
	x := 7
	n := -1
	ch := make(chan int, 1)
	ch <- 3
	var jv interface{} = []int{1}
	cs := []chan int{}
	obj := &T{}
	run("a-assertLeftCall", func() int { return iv.(int) + wit(5) })
	run("b-indexLeftCall", func() int { return s[i] + wit(5) })
	run("c-derefLeftCall", func() int { return *p + wit(5) })
	run("d-divLeftCall", func() int { return x/z + wit(5) })
	run("e-assertMiddle", func() int { return wit(1) + iv.(int) + wit(2) })
	run("f-indexMiddle", func() int { return wit(1) + s[i] + wit(2) })
	run("g-assertLeftRecv", func() int { return iv.(int) + <-ch })
	run("i-twoIndexLeftCall", func() int { return s[i] + t[k] + wit(5) })
	run("i2-indexAssertLeftCall", func() int { return s[i] + iv.(int) + wit(5) })
	run("i3-assertIndexLeftCall", func() int { return iv.(int) + s[i] + wit(5) })
	run("j-assertArgSibling", func() int { return sink(iv.(int), wit(7)) })
	run("j2-indexArgSibling", func() int { return sink(s[i], wit(7)) })
	run("k-compositeLit", func() int { return []int{iv.(int), wit(7)}[0] })
	run("k2-compositeLitIndex", func() int { return []int{s[i], wit(7)}[0] })
	run("l-returnList", func() int { a, b := func() (int, int) { return iv.(int), wit(7) }(); return a + b })
	run("m-sendChanIndex", func() int { cs[i] <- wit(7); return 0 })
	run("n-assertVsMutatingCall", func() int { return iv.(int) + func() int { iv = 4; return 1 }() })
	run("o-indexVsFixingCall", func() int { j := 9; return t[j] + func() int { j = 0; return 1 }() })
	run("p-sliceLeftCall", func() int { return len(s[i:]) + wit(5) })
	run("p2-shiftLeftCall", func() int { return x<<n + wit(5) })
	run("p3-ifaceCmpLeftCall", func() int { if jv == jv { return wit(5) }; return 0 })
	run("p4-convLeftCall", func() int { return [2]int(s)[0] + wit(5) })
	run("r-assertLeftMethod", func() int { return iv.(int) + obj.M() })
	run("s-assertLeftMinInline", func() int { return iv.(int) + min(t[k], 1) })
	run("u-assertRightCall", func() int { return wit(5) + iv.(int) })
	run("v-indexLeftCallArgPanics", func() int { return s[i] + wit(t[k]) })
	run("w-assertLeftMakeSlice", func() int { return iv.(int) + len(make([]int, t[k])) })
	run("w2-assertLeftLenIndexCall", func() int { return iv.(int) + len(t[k:]) + wit(5) })
	run("x-derefLeftIndexArgCall", func() int { return *p + wit(t[k]) })
	run("y-assertLeftNewCall", func() int { return iv.(int) + *new(int) + wit(5) })
	run("z-assertLeftAppend", func() int { return iv.(int) + len(append(s, t[k])) + wit(5) })
	run("z2-assertLeftCopy", func() int { d := []int{1, 2, 3}; return iv.(int) + copy(d[t[k]:], s) })
}
