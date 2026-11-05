// Defect-neighbourhood campaign, shape S29 (synthetic-symbol bookkeeping; members
// BUG-031/027, and BUG-302 fixed in train 28), lane sweep/s28-s29-spelling-symbols,
// 2026-11-05 (docs/2026-10-27_defect-neighbourhood-campaign.md §4). The emitter's
// temporaries — the call hoist `$c`, the switch `$sw`/`$swi`/`$swf`, the type-switch
// `$ts`/`$tsv`/`$tso`, the goto `$pc`/`$goto`, the multi-value `$mv`, the per-iteration
// `$lvp`/`$lvf`, the assign-form range `$rangeKey`/`$rangeVal`, the select temps and the
// fmt desugar's `$fmt` — twice in one function, in a func literal nested inside the same
// construct, nested, and in a generic function at two instantiations; expected = gc.

package main

import "fmt"

var cnt int

func f() int { cnt++; return cnt }
func g() int { cnt += 10; return cnt }
func add(a, b int) int { return a + b }
func pair() (int, int) { return 3, 4 }

type myI int

func hoistsTwoStatements() int {
	cnt = 0
	a := add(f(), g())
	b := add(g(), f())
	return a*100 + b // 1200+... gc decides
}

func hoistInLiteralInsideHoist() int {
	cnt = 0
	n := add(func() int { return add(f(), g()) }(), f())
	return n
}

func gHoist[T ~int](v T) T {
	cnt = 0
	return T(add(f(), int(v))) + T(add(g(), int(v)))
}

func hoistInGenericTwoInsts() int {
	return int(gHoist(1)) + int(gHoist(myI(2)))*1000
}

func switchesTwiceNestedAndLiteral() int {
	x, y := 1, 2
	n := 0
	switch x {
	case 1:
		n += 1
		fallthrough
	case 2:
		n += 10
	}
	switch y {
	case 2:
		n += 100
	}
	switch x {
	case 1:
		switch y {
		case 2:
			n += 1000
		}
		func() {
			switch y {
			case 2:
				n += 10000
				fallthrough
			case 3:
				n += 100000
			}
		}()
	}
	return n // 111111
}

func gSwitch[T ~int](v T) int {
	switch v {
	case 1:
		return 1
	case 2:
		return 2
	}
	return 0
}

func switchInGenericTwoInsts() int { return gSwitch(1) + gSwitch(myI(2))*10 } // 21

func typeSwitchesNested() int {
	var x any = 1
	var y any = "ab"
	n := 0
	switch v := x.(type) {
	case int:
		switch w := y.(type) {
		case string:
			n += v + len(w)
		}
		func() {
			switch w := y.(type) {
			case string:
				n += len(w) * 10
			}
		}()
	}
	switch v := y.(type) {
	case string:
		n += len(v) * 100
	}
	return n // 223
}

func gotoTwoLabels() int {
	n := 0
	goto a
a:
	n++
	if n < 3 {
		goto a
	}
	goto b
b:
	n += 10
	return n // 13
}

func multiValueTemps() int {
	a, b := pair()
	c, d := pair()
	n := add(pair()) + add(pair())
	func() {
		e, fv := pair()
		n += e + fv
	}()
	return a + b + c + d + n // 14 + 14 + 7 = 35
}

func gMV[T ~int](v T) T { a, b := pair(); return T(a+b) + v }

func multiValueInGenericTwoInsts() int { return int(gMV(1)) + int(gMV(myI(2)))*100 } // 908

func loopVarCapturesTwiceNested() int {
	var fs []func() int
	for i := 0; i < 2; i++ {
		fs = append(fs, func() int { return i })
	}
	for j := 0; j < 2; j++ {
		for k := 0; k < 2; k++ {
			fs = append(fs, func() int { return j*10 + k })
		}
	}
	for i := 0; i < 2; i++ {
		func() {
			for j := 0; j < 2; j++ {
				fs = append(fs, func() int { return i*100 + j })
			}
		}()
	}
	n := 0
	for _, fn := range fs {
		n += fn()
	}
	return n // 1 + (0+1+10+11) + (0+1+100+101) = 225
}

func gLoopVar[T ~int](v T) T {
	var fs []func() T
	for i := 0; i < 2; i++ {
		fs = append(fs, func() T { return T(i) + v })
	}
	return fs[0]() + fs[1]()
}

func loopVarInGenericTwoInsts() int { return int(gLoopVar(1)) + int(gLoopVar(myI(2)))*10 } // 3 + 50

func rangeAssignNested() int {
	s := []int{1, 2}
	var i, j, v int
	n := 0
	for i = range s {
		for j, v = range s {
			n += i*100 + j*10 + v
		}
		func() {
			for j = range s {
				n += 1000
			}
		}()
	}
	return n // (1+12+101+112) + 4000 = 4226
}

func selectsTwiceNested() int {
	a := make(chan int, 1)
	b := make(chan int, 1)
	a <- 1
	b <- 2
	n := 0
	select {
	case v := <-a:
		n += v
		func() {
			select {
			case w := <-b:
				n += w * 10
			}
		}()
	}
	a <- 3
	select {
	case v := <-a:
		n += v * 100
	}
	return n // 321
}

func gSelect[T ~int](v T) T {
	ch := make(chan T, 1)
	ch <- v
	select {
	case w := <-ch:
		return w * 2
	}
}

func selectInGenericTwoInsts() int { return int(gSelect(1)) + int(gSelect(myI(2)))*10 } // 42

type tF struct{}
type tG struct{}

func (tF) s() string { return fmt.Sprintf("%d", 1) }
func (tG) s() string { return fmt.Sprintf("%d%d", 2, 3) }

var fmtInit string

func init() { fmtInit = fmt.Sprintf("%v", true) }

func gFmt[T ~int](v T) string { return fmt.Sprintf("%d", int(v)) }

func fmtLiftsScopes() int {
	a := fmt.Sprintf("%d", 12)
	b := fmt.Sprintf("%s-%d", "x", 3)
	c := func() string { return fmt.Sprintf("%v", 1234) }()
	return len(a) + len(b)*10 + len(c)*100 + len(tF{}.s())*1000 + len(tG{}.s())*10000 + len(fmtInit)*100000 + len(gFmt(5))*1000000 + len(gFmt(myI(55)))*10000000 // 2+30+400+1000+20000+400000+1000000+20000000
}

func main() {
	println("hoistsTwoStatements", hoistsTwoStatements())
	println("hoistInLiteralInsideHoist", hoistInLiteralInsideHoist())
	println("hoistInGenericTwoInsts", hoistInGenericTwoInsts())
	println("switchesTwiceNestedAndLiteral", switchesTwiceNestedAndLiteral())
	println("switchInGenericTwoInsts", switchInGenericTwoInsts())
	println("typeSwitchesNested", typeSwitchesNested())
	println("gotoTwoLabels", gotoTwoLabels())
	println("multiValueTemps", multiValueTemps())
	println("multiValueInGenericTwoInsts", multiValueInGenericTwoInsts())
	println("loopVarCapturesTwiceNested", loopVarCapturesTwiceNested())
	println("loopVarInGenericTwoInsts", loopVarInGenericTwoInsts())
	println("rangeAssignNested", rangeAssignNested())
	println("selectsTwiceNested", selectsTwiceNested())
	println("selectInGenericTwoInsts", selectInGenericTwoInsts())
	println("fmtLiftsScopes", fmtLiftsScopes())
}
