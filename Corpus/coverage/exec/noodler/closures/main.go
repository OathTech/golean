// noodler probes — closures and the Go 1.22 per-iteration loop
// variable (spec#For_clause: "each iteration has its own separate
// declared variable ... The variable used by the first iteration is
// declared by the init statement. The variable used by each subsequent
// iteration is declared implicitly before executing the post statement
// and initialized to the value of the previous iteration's variable at
// that moment").
package main

import "sync"

// Body modification is copied into the next iteration's variable; the
// closure sees the body-modified value of ITS iteration.
func threeClauseBodyModification() (int, int, int, int) {
	var fs []func() int
	for i := 0; i < 5; i++ {
		if i == 1 {
			i += 2
		}
		fs = append(fs, func() int { return i })
	}
	return len(fs), fs[0](), fs[1](), fs[2]()
}

// A closure modifying its per-iteration variable after the loop does
// not affect siblings.
func closureModifiesOwnIteration() int {
	var fs []func() int
	for i := range 3 {
		fs = append(fs, func() int { i += 10; return i })
	}
	return fs[0]() + fs[1]() + fs[2]() + fs[0]()
}

// Defers in a loop capture per-iteration variables; LIFO order.
func defersCapturePerIteration() (r int) {
	for i := 0; i < 3; i++ {
		defer func() { r = r*10 + i }()
	}
	return 0
}

// A deferred closure that modifies the loop variable modifies only its
// own copy.
func deferModifiesLoopVar() (r int) {
	for i := 0; i < 3; i++ {
		defer func() { i *= 10; r += i }()
	}
	return 0
}

// Goroutines capturing the per-iteration variable, joined by a
// WaitGroup and protected by a Mutex.
func goroutinesCaptureLoopVar() int {
	var wg sync.WaitGroup
	var mu sync.Mutex
	sum := 0
	for i := 1; i <= 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			mu.Lock()
			sum += i
			mu.Unlock()
		}()
	}
	wg.Wait()
	return sum
}

// Assigning to the range-over-int variable in the body does not change
// the iteration count.
func rangeIntBodyAssign() (int, int) {
	sum, count := 0, 0
	for i := range 5 {
		i += 2
		sum += i
		count++
	}
	return sum, count
}

// Three-clause body assignment DOES change the iteration count.
func threeClauseBodyAssignCount() (int, int) {
	count, last := 0, 0
	for i := 0; i < 10; i++ {
		i += 3
		count++
		last = i
	}
	return count, last
}

// A closure called in a return expression that writes the named result:
// the return value wins.
func closureWritesNamedResultInReturn() (r int) {
	f := func() int { r = 5; return 1 }
	return f()
}

// Recursive closure via a declared func variable.
func recursiveClosure() int {
	var fib func(int) int
	fib = func(n int) int {
		if n < 2 {
			return n
		}
		return fib(n-1) + fib(n-2)
	}
	return fib(15)
}

// Generators are independent.
func independentGenerators() (int, int) {
	gen := func() func() int {
		n := 0
		return func() int { n++; return n }
	}
	a, b := gen(), gen()
	a()
	a()
	return a(), b()
}

// Closures capture variables, not values.
func captureByReference() (int, int) {
	type S struct{ v int }
	s := S{1}
	f := func() int { return s.v }
	before := f()
	s.v = 2
	return before, f()
}

// Immediately-invoked function literal.
func immediateInvocation() int {
	return func(a int) int { return a * 2 }(21) + func() int { return 1 }()
}

// The range expression is evaluated once; appending to the ranged slice
// inside the body does not extend the iteration.
func rangeEvaluatedOnceAppend() (int, int) {
	s := []int{1, 2, 3}
	sum := 0
	for i, v := range s {
		if i == 0 {
			s = append(s, 100)
		}
		sum += v
	}
	return sum, len(s)
}

// Loop condition is a closure reading captured state.
func conditionClosure() int {
	n := 0
	cond := func() bool { n++; return n < 4 }
	count := 0
	for cond() {
		count++
	}
	return count*10 + n
}

// A closure captured in a switch clause sees the case-scoped variable.
func closureInSwitchClause(x int) int {
	var f func() int
	switch y := x * 2; {
	case y > 5:
		f = func() int { return y + 1 }
	default:
		f = func() int { return y - 1 }
	}
	return f()
}

// Closure capturing a variable declared in an if-init, called after the
// if statement finished.
func closureCapturesIfInit() int {
	var f func() int
	if v := 7; v > 3 {
		f = func() int { v++; return v }
	}
	return f() + f()
}

// Variadic closure and spread.
func variadicClosure() int {
	sum := func(xs ...int) int {
		t := 0
		for _, x := range xs {
			t += x
		}
		return t
	}
	nums := []int{1, 2, 3}
	return sum(nums...) + sum() + sum(4)
}

// Per-iteration variable and `continue`: the post statement runs on the
// fresh copy.
func continueWithPerIteration() int {
	var fs []func() int
	for i := 0; i < 4; i++ {
		if i%2 == 1 {
			continue
		}
		fs = append(fs, func() int { return i })
	}
	return fs[0]()*10 + fs[1]()
}

// Range over a string: per-iteration index and rune captured.
func rangeStringCapture() int {
	var fs []func() int
	for i, r := range "héllo" {
		fs = append(fs, func() int { return i*1000 + int(r) })
	}
	return fs[1]() + fs[2]()
}

// Two closures share one variable declared outside the loop.
func sharedOuterVariable() int {
	total := 0
	var fs []func()
	for i := 0; i < 3; i++ {
		fs = append(fs, func() { total += i })
	}
	for _, f := range fs {
		f()
	}
	return total
}

func main() {}
