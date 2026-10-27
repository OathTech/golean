// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// for conditions and post statements per iteration (the condition n+1 times, the post n
// times, never hoisted out of the loop), a len of a call in the condition, a read-modify-
// write with a call in the post, calls in init/cond/post, a receive as the condition, the
// comma-ok map lookup with calls in an if-init, in a closure and in a generic function.

package main

var cnt int

var condCalls, postCalls int

func f() int { cnt++; return 1 }

func fs() []int { cnt++; return []int{1, 2, 3} }

func fm() map[int]int { cnt++; return map[int]int{1: 5} }

func fk() int { cnt++; return 1 }

func cond(i int) bool { condCalls++; return i < 3 }

func post() { postCalls++ }

func condPostCounts() int {
	condCalls, postCalls = 0, 0
	n := 0
	for i := 0; cond(i); i++ {
		post()
		n++
	}
	return condCalls*100 + postCalls*10 + n
}

func condOnly() int {
	condCalls = 0
	i := 0
	for cond(i) {
		i++
	}
	return condCalls*100 + i
}

func lenCallCond() int {
	cnt = 0
	n := 0
	for i := 0; i < len(fs()); i++ {
		n++
	}
	return cnt*100 + n
}

func postRmwCall() int {
	cnt = 0
	s := []int{0, 10}
	n := 0
	for i := 0; i < 3; s[f()]++ {
		i++
		n++
	}
	return cnt*100 + s[1]
}

func initCondPostCalls() int {
	cnt = 0
	g := func(x int) int { cnt++; return x + 1 }
	n := 0
	for x := f(); x < 3; x = g(x) {
		n++
	}
	return cnt*100 + n
}

func recvCond() int {
	ch := make(chan bool, 3)
	ch <- true
	ch <- true
	ch <- false
	n := 0
	for <-ch {
		n++
	}
	return len(ch)*100 + n
}

func commaOkMapCalls() int {
	cnt = 0
	r := 0
	if v, ok := fm()[fk()]; ok {
		r = v
	}
	return cnt*100 + r
}

func postCallInBody() int {
	cnt = 0
	n := 0
	for i := 0; i < 3; i += f() {
		n++
	}
	return cnt*100 + n
}

func closureFor() int {
	condCalls, postCalls = 0, 0
	n := 0
	inner := func() {
		for i := 0; cond(i); i++ {
			post()
			n++
		}
	}
	inner()
	return condCalls*100 + postCalls*10 + n
}

func forGeneric[T any](xs func() []T) int {
	n := 0
	for i := 0; i < len(xs()); i++ {
		n++
	}
	return n
}

func genericFor() int {
	cnt = 0
	r := forGeneric(fs)
	return cnt*100 + r
}

func main() {
	condPostCounts()
	condOnly()
	lenCallCond()
	postRmwCall()
	initCondPostCalls()
	recvCond()
	commaOkMapCalls()
	postCallInBody()
	closureFor()
	genericFor()
}
