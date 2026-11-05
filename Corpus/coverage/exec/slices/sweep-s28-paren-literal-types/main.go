// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised element and key
// types inside composite-literal, make, new, chan and pointer types; expected = gc go1.26.5.

package main

type pt struct{ v int }

func parenLiteralTypes() int {
	s := [](int){1, 2}
	s2 := []((int)){3}
	a := [2](int){4, 5}
	m := map[(string)](int){"k": 6}
	m2 := map[string]([]int){"k": {7, 8}}
	ps := []*(pt){{9}}
	ps2 := [](*pt){{10}}
	cs := [](chan int){make(chan int, 1)}
	cs[0] <- 11
	return s[1] + s2[0]*10 + a[1]*100 + m["k"]*1000 + m2["k"][1]*10000 + ps[0].v*100000 + ps2[0].v*1000000 + <-cs[0]*10000000 // 119868532
}

func parenMakeNewChanPtr() int {
	s := make(([]int), 3)
	c := make((chan int))
	m := make((map[string]int))
	p := new((int))
	q := new((pt))
	var rc chan (int) = make(chan (int), 1)
	var cc chan (<-chan int) = make(chan (<-chan int), 1)
	var pp *(pt) = &pt{3}
	var p2 (*pt) = pp
	*p = 2
	q.v = 4
	m["k"] = 5
	rc <- 6
	cc <- rc
	go func() { c <- 7 }()
	got := <-c
	return len(s) + *p*10 + q.v*100 + m["k"]*1000 + <-(<-cc)*10000 + pp.v*100000 + p2.v*1000000 + got*10000000 // 73365243
}

func main() {
	println("parenLiteralTypes", parenLiteralTypes())
	println("parenMakeNewChanPtr", parenMakeNewChanPtr())
}
