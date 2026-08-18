package main

// spec#Conversions block Conversions-2-afcd996f: parenthesization
// disambiguates conversions from other syntax — (*Point)(p) converts,
// (<-chan int)(c) converts to a receive-only channel while <-chan int(c)
// parses as a RECEIVE from the conversion chan int(c), and func() int(x) is
// an UNAMBIGUOUS conversion to func() int (as is the parenthesized
// (func() int)(x)). The block's pure parse annotations with no executable
// reading (*Point(p) as *(Point(p)); func()(x) as a signature) are noted, not
// run.

type Point struct{ x, y int }

func conversionParseForms() int {
	p := &Point{1, 2}
	pp := (*Point)(p) // p is converted to *Point
	ch := make(chan int, 2)
	rc := (<-chan int)(ch) // ch is converted to <-chan int
	ch <- 7
	v := <-rc
	ch <- 9
	w := <-chan int(ch) // same as <-(chan int(ch)): a receive, not a type
	x := func() int { return 3 }
	f1 := (func() int)(x)                               // x is converted to func() int
	f2 := (func() int)(x)                               // x is converted to func() int (unambiguous)
	return pp.x*10000 + v*1000 + w*100 + f1()*10 + f2() // 17933
}
