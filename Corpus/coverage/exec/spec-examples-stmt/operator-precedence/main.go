package main

// spec#Operator_precedence block Operator_precedence-2-c640b54b: each
// line's unparenthesized expression means exactly its parenthesized
// reading:
//   +x               == x
//   42 + a - b       == (42 + a) - b   (same-precedence, left assoc)
//   23 + 3*x[i]      == 23 + (3 * x[i])  (NOT (23+3)*x[i])
//   x <= f()         == x <= f()
//   ^a >> b          == (^a) >> b        (NOT ^(a >> b))
//   f() || g()       == f() || g()
//   x == y+1 && <-chanInt > 0 == (x == (y+1)) && ((<-chanInt) > 0)
// Values are chosen so each wrong grouping yields a DIFFERENT value:
//   unaryPlus: x=17 -> 17
//   addSub: a=100,b=7 -> 135 (both groupings agree; left-assoc pinned
//     by the machine matching Go exactly)
//   mulIndex: x[1]=5 -> 23+15 = 38 (wrong grouping: 26*5 = 130)
//   cmpCall: 3 <= 4 -> true
//   notShift: a,b uint8 = 2,1 -> (^2)>>1 = 253>>1 = 126 (wrong: ^1 = 254)
//   orCalls: true || (g not needed) -> true, calls == 1 (short-circuit)
//   mixed: x=3,y=2, chan holds 5 -> (3==3) && (5>0) -> true

func opPrecUnaryPlus() int {
	x := 17
	return +x // x
}

func opPrecAddSub() int {
	a, b := 100, 7
	return 42 + a - b // (42 + a) - b
}

func opPrecMulIndex() int {
	x := []int{9, 5, 2}
	i := 1
	return 23 + 3*x[i] // 23 + (3 * x[i])
}

func opPrecCmpCall() bool {
	x := 3
	f := func() int { return 4 }
	return x <= f() // x <= f()
}

func opPrecNotShift() int {
	var a, b uint8 = 2, 1
	return int(^a >> b) // (^a) >> b
}

func opPrecOrCalls() (bool, int) {
	calls := 0
	f := func() bool { calls++; return true }
	g := func() bool { calls += 10; return false }
	r := f() || g() // f() || g(); || short-circuits, so g is not called
	return r, calls
}

func opPrecMixed() bool {
	x, y := 3, 2
	chanInt := make(chan int, 1)
	chanInt <- 5
	return x == y+1 && <-chanInt > 0 // (x == (y+1)) && ((<-chanInt) > 0)
}

func main() {
	opPrecMixed()
}
