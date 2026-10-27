package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: a PACKAGE-LEVEL name
// shadowed by a local (the self-referential define reads the global — BUG-142's
// shape at a package-level outer), a parameter, a named result, a receiver, a
// local type / const, a for-init variable whose address escapes, a type-switch
// guard, a range variable, a select-case variable, and inside init(); a package
// function and a package type shadowed by locals; a closure over the global
// declared before a local shadow; the global written through a call under a
// live shadow. emitIdent routes a package variable through its seeded cell and
// a local through the frame. Expected = gc go1.26.5.

var g = 10
var gf = 0

type T struct{ v int }

func (g T) receiverShadow() int { return g.v }

func pkgFunc() int { return 5 }

func mk() int {
	g := 3 // the initializer's function shadows the global it initializes
	return g * 2
}

var g2 = mk()

func init() {
	g := 100
	_ = g
	gf = 1
}

func readG() int { return g }

func bumpGlobal() { g++ }

// C1
func selfShadowReadsGlobal() int {
	g := g + 1 // 11
	return g
}

func paramShadow(g int) int { return g * 2 }

// C2
func paramShadowCell() int { return paramShadow(3)*100 + g } // 610

func resultShadow() (g int) { return } // the result's zero, not the global

// C3
func resultShadowCell() int { return resultShadow()*100 + g } // 10

// C4
func receiverShadowCell() int { return T{7}.receiverShadow()*100 + g } // 710

// C5
func closureGlobalVsLocal() int {
	f := func() int { return g }
	g := 20
	return f()*100 + g // 1020
}

// C6
func globalWrittenUnderShadow() int {
	g := 1
	bumpGlobal()
	r := g
	return r*100 + readG() // 111
}

// C7
func localTypeShadowsGlobalVar() int {
	type g int
	x := g(4)
	return int(x) * 2 // 8
}

// C8
func localConstShadowsGlobal() int {
	const g = 30
	return g + 1 // 31
}

// C9
func localVarShadowsFunc() int {
	a := pkgFunc()
	pkgFunc := func() int { return 6 }
	return a*10 + pkgFunc() // 56
}

// C10
func localVarShadowsType() int {
	t := T{v: 2}
	T := 3
	return t.v*10 + T // 23
}

// C11
func forInitAddrShadow() int {
	var ps []*int
	for g := 0; g < 3; g++ {
		ps = append(ps, &g)
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2] + g // 22
}

// C12
func initFromFuncWithShadow() int { return g2*100 + g } // 610

// C14
func shadowInInit() int { return g*10 + gf } // 101

// C15
func tsGuardShadow() int {
	var x any = 7
	switch g := x.(type) {
	case int:
		return g*100 + readG() // 710
	}
	return -1
}

// C16
func rangeVarShadow() int {
	sum := 0
	for g := range 3 {
		sum += g
	}
	return sum*100 + g // 310
}

// C17
func selectCaseShadow() int {
	ch := make(chan int, 1)
	ch <- 4
	select {
	case g := <-ch:
		return g*100 + readG() // 410
	}
}

func main() {
	println(selfShadowReadsGlobal(), paramShadowCell(), resultShadowCell(), receiverShadowCell(),
		closureGlobalVsLocal(), globalWrittenUnderShadow(), localTypeShadowsGlobalVar(),
		localConstShadowsGlobal(), localVarShadowsFunc(), localVarShadowsType(), forInitAddrShadow(),
		initFromFuncWithShadow(), shadowInInit(), tsGuardShadow(), rangeVarShadow(), selectCaseShadow())
}
