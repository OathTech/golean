package main

// S23 sweep — resource budgets (docs/defect-shapes.md; the plan
// docs/2026-10-27_defect-neighbourhood-campaign.md §4; lane sweep/s23-budgets,
// 2026-11-05): the DEPTH doors — the machine's own recursion over the
// program's shapes, where a native stack overflow would be an unnamed stop.
// Every row runs at a depth the gate's wall admits; the deeper measurements
// (recursion 10^5, boxed values 10^5, 10^4 goroutines) are the grind BUG-411
// records. gc answers on every row.
//
//   recursion1e4            — plain recursion 10^4 deep.
//   recursionDeferPanic1e4  — a defer in every frame and a panic at the bottom
//                             recovered at the top: the drains and the recover
//                             walk over 10^4 frames.
//   recursionMethodClosure  — a method and a closure each recursing 5000 deep.
//   recursionGoroutine3000  — recursion 3000 deep in a child goroutine.
//   exprNesting500          — a binary expression nested 500 deep (generated).
//   callNesting500          — a call nested 500 deep (generated).
//   literalNesting500       — a composite literal nested 500 deep (generated),
//                             walked by type assertions.
//   defers1e4               — 10^4 deferred calls in one frame, drained at
//                             return.
//   list1e4                 — a 10^4-node linked list built and walked.
//   boxedNesting1e3         — a value boxed 1000 deep (x = S{x}), compared with
//                             == against its twin and walked by assertions.

type S struct{ in any }

type Node struct {
	v    int
	next *Node
}

type T struct{ k int }

var drained int

func down(n int) int {
	if n == 0 {
		return 0
	}
	return 1 + down(n-1)
}

func downDefer(n int) int {
	defer func() { drained++ }()
	if n == 0 {
		panic("bottom")
	}
	return 1 + downDefer(n-1)
}

func (t T) down(n int) int {
	if n == 0 {
		return t.k
	}
	return 1 + t.down(n-1)
}

func f(x int) int { return x + 1 }

func depth(v any) int {
	if s, ok := v.([]any); ok {
		return 1 + depth(s[0])
	}
	return 0
}

func recursion1e4() int { return down(10000) }

func recursionDeferPanic1e4() (r int) {
	drained = 0
	defer func() {
		if e := recover(); e != nil {
			r = drained*10 + len(e.(string))
		}
	}()
	return downDefer(10000)
}

func recursionMethodClosure() int {
	var cl func(int) int
	cl = func(n int) int {
		if n == 0 {
			return 0
		}
		return 1 + cl(n-1)
	}
	return T{3}.down(5000)*10 + cl(5000)
}

func recursionGoroutine3000() int {
	c := make(chan int)
	go func() { c <- down(3000) }()
	return <-c
}

func exprNesting500() int {
	x := (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
	return x
}

func callNesting500() int {
	return f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
}

func literalNesting500() int {
	v := []any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{[]any{1}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
	return depth(v)
}

func defers1e4() (r int) {
	for i := 0; i < 10000; i++ {
		defer func() { r++ }()
	}
	return 5
}

func list1e4() int {
	var head *Node
	for i := 0; i < 10000; i++ {
		head = &Node{v: i, next: head}
	}
	n := 0
	for p := head; p != nil; p = p.next {
		n += p.v & 1
	}
	return n
}

func boxedNesting1e3() int {
	var x any = 0
	var y any = 0
	for i := 0; i < 1000; i++ {
		x = S{x}
		y = S{y}
	}
	eq := 0
	if x == y {
		eq = 1
	}
	d := 0
	for {
		if s, ok := x.(S); ok {
			x = s.in
			d++
		} else {
			break
		}
	}
	return d*10 + eq
}

func main() {
	println(recursion1e4(), recursionDeferPanic1e4(), recursionMethodClosure(), recursionGoroutine3000(),
		exprNesting500(), callNesting500(), literalNesting500(), defers1e4(), list1e4(), boxedNesting1e3())
}
