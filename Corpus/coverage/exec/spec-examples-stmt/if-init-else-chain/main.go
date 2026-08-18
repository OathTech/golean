package main

// spec#If_statements block If_statements-3-23172299: "the expression
// may be preceded by a simple statement, which executes before the
// expression is evaluated":
//   if x := f(); x < y { return x } else if x > z { return z }
//   else { return y }
// With y = 10, z = 20 and f returning its argument, the three
// outcomes are: f() < 10 returns f()'s value; f() > 20 returns 20;
// otherwise returns 10. Expected: arg 5 -> 5, arg 25 -> 20,
// arg 15 -> 10, boundary arg 10 -> 10, boundary arg 20 -> 10.

func ifInitElseChain(v int) int {
	y, z := 10, 20
	f := func() int { return v }
	if x := f(); x < y {
		return x
	} else if x > z {
		return z
	} else {
		return y
	}
}

func main() {
	ifInitElseChain(5)
}
