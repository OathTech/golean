// noodler probes — defer/recover shapes at the edge of "called directly
// by a deferred function" (spec#Handling_panics), panic payload kinds,
// and panics in goroutines.
package main

type rec struct{ v int }

// recover called by a deferred METHOD (directly deferred) works.
func (r *rec) recoverMethod() {
	if recover() != nil {
		r.v = 1
	}
}

func deferredMethodRecovers() (out int) {
	r := &rec{}
	defer func() { out = r.v * 10 }()
	defer r.recoverMethod()
	panic("m")
}

// A method VALUE stored in a variable and deferred: still the deferred
// function itself, so recover works.
func deferredMethodValueRecovers() (out int) {
	r := &rec{}
	defer func() { out = r.v * 100 }()
	f := r.recoverMethod
	defer f()
	panic("mv")
}

// recover called through a func VALUE inside the deferred closure is not
// "directly by the deferred function": returns nil, the panic proceeds.
func recoverViaFuncValueIndirect() int {
	g := func() any { return recover() }
	defer func() {
		_ = g()
	}()
	panic("indirect-value")
}

// A deferred closure calling recover through a function literal
// invoked immediately: also indirect.
func recoverViaImmediateLiteral() int {
	defer func() {
		func() { _ = recover() }()
	}()
	panic("immediate")
}

// Panic payload is a struct; fields observable after recover.
type payload struct {
	code int
	msg  string
}

func panicStructPayload() (int, string) {
	var c int
	var m string
	func() {
		defer func() {
			if p, ok := recover().(payload); ok {
				c, m = p.code, p.msg
			}
		}()
		panic(payload{42, "hi"})
	}()
	return c, m
}

// Panic payload is a pointer to a struct; recovered pointer aliases.
func panicPointerPayload() int {
	p := &payload{1, ""}
	func() {
		defer func() {
			if q, ok := recover().(*payload); ok {
				q.code += 10
			}
		}()
		panic(p)
	}()
	return p.code
}

// Custom error payload recovered and its Error() called.
type myErr struct{ n int }

func (e myErr) Error() string { return "myerr" }

func panicCustomErrorPayload() (string, int) {
	var s string
	var n int
	func() {
		defer func() {
			r := recover()
			if e, ok := r.(myErr); ok {
				s = e.Error()
				n = e.n
			}
		}()
		panic(myErr{3})
	}()
	return s, n
}

// Deferred builtins run at function exit: close ...
func deferredClose() (int, bool) {
	ch := make(chan int, 1)
	func() {
		defer close(ch)
		ch <- 5
	}()
	v := <-ch
	_, ok := <-ch
	return v, ok
}

// ... and delete.
func deferredDelete() int {
	m := map[int]int{1: 1, 2: 2}
	func() {
		defer delete(m, 1)
		m[3] = 3
	}()
	return len(m)*10 + m[3]
}

// An unrecovered panic in a child goroutine aborts the whole program
// while main is blocked on a receive.
func goroutinePanicAborts() int {
	ch := make(chan int)
	go func() {
		panic("child-boom")
	}()
	return <-ch
}

// A child goroutine recovers its own panic and reports through a channel.
func goroutineRecoversOwnPanic() int {
	ch := make(chan int)
	go func() {
		defer func() {
			if r := recover(); r != nil {
				ch <- 7
			}
		}()
		panic("own")
	}()
	return <-ch
}

// A panic in main is NOT recoverable from a child goroutine's deferred
// recover; here the child finishes first, main then panics.
func panicNotCrossGoroutine() int {
	done := make(chan bool)
	go func() {
		defer func() { recover(); done <- true }()
	}()
	<-done
	panic("main-boom")
}

// Nested panics recovered at two levels return distinct values.
func nestedRecoverLevels() (int, int) {
	inner, outer := 0, 0
	func() {
		defer func() {
			if r := recover(); r != nil {
				outer = r.(int)
			}
		}()
		func() {
			defer func() {
				if r := recover(); r != nil {
					inner = r.(int)
					panic(r.(int) + 1)
				}
			}()
			panic(10)
		}()
	}()
	return inner, outer
}

// recover after a deferred call already recovered: nil.
func secondDeferSeesNil() int {
	r := 0
	func() {
		defer func() {
			if recover() == nil {
				r += 1
			}
		}()
		defer func() {
			if recover() != nil {
				r += 10
			}
		}()
		panic("x")
	}()
	return r
}

// Deferred function arguments are evaluated at defer time, but a
// closure body sees the final values.
func deferArgsVsClosure() (int, int) {
	a, b := 0, 0
	func() {
		x := 1
		defer func(v int) { a = v }(x)
		defer func() { b = x }()
		x = 2
	}()
	return a, b
}

// A panic with a nil-interface payload in Go 1.21+ recovers as a
// runtime.PanicNilError (non-nil).
func panicNilRecovered() bool {
	got := false
	func() {
		defer func() { got = recover() != nil }()
		panic(nil)
	}()
	return got
}

// Panicking inside a deferred function's own defer chain.
func panicInsideDeferredDefer() int {
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 1
			}
		}()
		defer func() {
			defer func() {
				if recover() != nil {
					r = 2
				}
			}()
			panic("inner")
		}()
	}()
	return r
}

// A recovered panic inside a loop lets the loop continue.
func recoverInLoopContinues() int {
	count := 0
	for i := 0; i < 5; i++ {
		func() {
			defer func() { recover() }()
			if i%2 == 0 {
				panic(i)
			}
			count++
		}()
	}
	return count
}

func main() {}
