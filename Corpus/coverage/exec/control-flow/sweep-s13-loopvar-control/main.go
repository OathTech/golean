package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the per-iteration
// for-clause variable (BUG-003's carrier-pointer lowering) against the
// control forms around it — deferred closures and deferred arguments,
// continue / break / a labeled continue from an inner loop, the body writing
// the variable before the post statement copies it, nested and two-variable
// loops, a redeclaration in the body, a loop with no post statement, a
// multi-value-call init, a literal parameter shadowing the loop variable, and
// the whole shape inside a nested closure. Expected = gc go1.26.5.

var seq = 0

func next() (int, bool) {
	seq++
	return seq * 10, seq <= 3
}

// D4: a deferred closure per iteration (LIFO at exit).
func deferClosureCapture() (sum int) {
	for i := 0; i < 3; i++ {
		defer func() { sum = sum*10 + i }()
	}
	return // 210
}

// D4b: a deferred argument evaluated at defer time (the plain path).
func deferArgPlain() (sum int) {
	add := func(v int) { sum = sum*10 + v }
	for i := 0; i < 3; i++ {
		defer add(i)
	}
	return // 210
}

// D5: continue around a capture.
func continueCapture() int {
	var fs []func() int
	for i := 0; i < 5; i++ {
		if i%2 == 1 {
			continue
		}
		fs = append(fs, func() int { return i })
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 24
}

// D6: break after a capture.
func breakCapture() int {
	var f func() int
	for i := 0; i < 10; i++ {
		f = func() int { return i }
		if i == 3 {
			break
		}
	}
	return f() // 3
}

// D8: the body writes the iteration's cell; the post runs on the next iteration's copy.
func bodyMutationPostCopy() int {
	var fs []func() int
	for i := 0; i < 5; i++ {
		i++
		fs = append(fs, func() int { return i })
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 135
}

// D9: nested loops, both variables captured.
func nestedBothCaptured() int {
	var fs []func() int
	for i := 0; i < 2; i++ {
		for j := 0; j < 2; j++ {
			fs = append(fs, func() int { return i*10 + j })
		}
	}
	return fs[0]()*1000000 + fs[1]()*10000 + fs[2]()*100 + fs[3]() // 11011
}

// D10: two loop variables captured.
func twoVarsCaptured() int {
	var fs []func() int
	for i, j := 0, 10; i < j; i, j = i+1, j-1 {
		fs = append(fs, func() int { return i*100 + j })
	}
	return fs[0]() + fs[4]() // 416
}

// D11 / E10: redeclared in the body, then mixed-redeclared.
func bodyRedeclare() int {
	var fs []func() int
	for i := 0; i < 3; i++ {
		i := i * 2
		i, k := i+1, i
		fs = append(fs, func() int { return i*10 + k })
	}
	return fs[0]()*10000 + fs[1]()*100 + fs[2]() // 103254
}

// D23: no post statement; the body increments.
func noPostBodyIncr() int {
	var fs []func() int
	for i := 0; i < 3; {
		fs = append(fs, func() int { return i })
		i++
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 123
}

// D24: a multi-value-call init and post.
func multiCallInit() int {
	var fs []func() int
	for v, ok := next(); ok; v, ok = next() {
		fs = append(fs, func() int { return v })
	}
	return fs[0]() + fs[1]() + fs[2]() // 60
}

// D28: a labeled continue from the inner loop to the outer per-iteration loop.
func labeledContinueOuter() int {
	var fs []func() int
outer:
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			if j == 1 {
				fs = append(fs, func() int { return i*10 + j })
				continue outer
			}
		}
	}
	return fs[0]()*10000 + fs[1]()*100 + fs[2]() // 11121
}

// D31: a literal parameter shadowing the loop variable (the plain path).
func litParamShadowsLoopvar() int {
	sum := 0
	for i := 0; i < 3; i++ {
		f := func(i int) int { return i * 2 }
		sum += f(i + 1)
	}
	return sum // 12
}

// X5: the per-iteration capture inside a nested closure.
func periterInClosure() int {
	run := func() int {
		var fs []func() int
		for i := 0; i < 3; i++ {
			fs = append(fs, func() int { return i })
		}
		return fs[0]()*100 + fs[1]()*10 + fs[2]()
	}
	return run() // 12
}

func main() {
	println(deferClosureCapture(), deferArgPlain(), continueCapture(), breakCapture(), bodyMutationPostCopy(),
		nestedBothCaptured(), twoVarsCaptured(), bodyRedeclare(), noPostBodyIncr(), multiCallInit(),
		labeledContinueOuter(), litParamShadowsLoopvar(), periterInClosure())
}
