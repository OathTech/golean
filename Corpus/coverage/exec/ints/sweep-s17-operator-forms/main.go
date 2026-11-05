package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-001's line): unary operator chains and binary operators mixed
// across every precedence level without parentheses — the associativity of
// the subtractive, shift, and-not and division operators, the remainder
// against multiplication and negation, chained comparisons, boolean
// equality chains, logical mixes, concatenation chains, bit mixes, a shift
// beside an addition; and the operators in a generic body.
// Expected = gc go1.26.5.

// B12.2
func unaryArithChains() int {
	x := 5
	return - -x*1000 + ^^x*100 + (-^x)*10 + (^-x) + (+ -x) + (- - -x) // 5000 + 500 + 60 + 4 - 5 - 5 = 5554
}

func unaryBoolChain() int {
	b := true
	r := 0
	if !!b {
		r = 1
	}
	if !!!b {
		r += 10
	}
	return r // 1
}

func unaryPtrChains() int {
	x := 7
	p := &x
	pp := &p
	ppp := &pp
	return *&x*100 + ***ppp*10 + **pp - *&*&x + *p*0 // 700 + 70 + 7 - 7 + 0 = 770
}

func unaryRecvUnder() int {
	ch := make(chan int, 3)
	ch <- 3
	ch <- 4
	ch <- 5
	bch := make(chan bool, 1)
	bch <- false
	r := -<-ch*100 + ^<-ch*10 + <-ch
	if !<-bch {
		r += 1000
	}
	return r // -300 + (-5)*10 + 5 + 1000 = 655
}

// B13.2
func arithMix() int {
	a, b, c, d, e := 1, 2, 3, 12, 4
	return a + b*c<<1 | d&^e // 1 + ((2*3)<<1) | (12 &^ 4) = 1 + 12 | 8 = 13 | 8 = 13
}

func assocSub() int {
	a, b, c := 10, 3, 2
	return a - b - c // 5
}

func assocShift() int {
	a, b, c := 1, 2, 3
	return a << b << c // (1<<2)<<3 = 32
}

func assocAndNot() int {
	a, b, c := 0xff, 0x0f, 0x30
	return a &^ b &^ c // (0xff &^ 0x0f) &^ 0x30 = 0xf0 &^ 0x30 = 0xc0 = 192
}

func assocDiv() int {
	a, b, c := 100, 5, 2
	return a / b / c // 10
}

func remMul() int {
	a, b, c := 17, 5, 3
	return a % b * c // (17 % 5) * 3 = 6
}

func negRem() int {
	x, y := 7, 3
	return -x % y // (-7) % 3 = -1
}

func compareChain() int {
	a, b, c, d := 1, 2, 3, 2
	r := 0
	if a < b == (c > d) {
		r = 1
	}
	if a+1 < b*2 == (c-1 >= d) {
		r += 10
	}
	return r // (1<2) == (3>2) → true == true; (2 < 4) == (2 >= 2) → 11
}

func boolEqChain() int {
	a, b := 2, 2
	r := 0
	if a == b == true {
		r = 1
	}
	if a != b != false {
		r += 10
	}
	return r // 1
}

func logicMix() int {
	a, b, c, d, e := 1, 2, 3, 4, false
	r := 0
	if a < b && b < c || c == d && !e {
		r = 1
	}
	if a > b || b > c && !e {
		r += 10
	}
	return r // 1
}

func concatChain() int {
	s, t := "a", "b"
	u := s + "x" + t + s
	return len(u)*100 + int(u[1]) // 400 + 120 = 520
}

func bitMix() int {
	x, y, z, w := 0x10, 0x03, 0x05, 0x06
	return x | y ^ z&w // 0x10 | (0x03 ^ (0x05 & 0x06)) = 0x10 | (3 ^ 4) = 0x10 | 7 = 23
}

func shiftPlus() int {
	a := 8
	return a>>1 + 1 // (8>>1) + 1 = 5
}

// B13.4
func opsG[T int | int64 | float64](a, b T) T {
	return a*b - a/b + (a - b)
}

func opsGF[T float64](a, b T) T {
	return a*b - a/b + (a - b)
}

func opsInGeneric() int {
	return int(opsG(7, 2)) + int(opsGF(7.0, 2.0)*10) // 14 - 3 + 5 = 16; (14 - 3.5 + 5)*10 = 155 → 171
}

func main() {
	println(unaryArithChains(), unaryBoolChain(), unaryPtrChains(), unaryRecvUnder(), arithMix(), assocSub(),
		assocShift(), assocAndNot(), assocDiv(), remMul(), negRem(), compareChain(), boolEqChain(), logicMix(),
		concatChain(), bitMix(), shiftPlus(), opsInGeneric())
}
