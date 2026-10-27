package main

// Sweep S12 — the RECOVER WALK: which frame's `recover()` sees the panic
// (matrix cells E04, E13, E14, E20, E21; lane sweep/s12-panic-recover,
// 2026-10-27). gc's rule (runtime/panic.go gorecover): recover returns the
// payload exactly when called directly by the function the panic sequence
// invoked as a deferred call. The machine: `recoverResult` walks glue to the
// first call frame and `recoverAtDeferred` demands the frame sit directly on
// the panic marker.

// A deferred FUNCTION VARIABLE holding a closure that calls recover directly.
func walkDeferFuncVar() int {
	r := 0
	func() {
		fv := func() {
			if recover() != nil {
				r = 1
			}
		}
		defer fv()
		panic("x")
	}()
	return r
}

// recover() in a closure deferred BY the deferred function (one frame too
// deep for gc's rule — the inner closure runs at the outer deferred
// function's own exit, not as the panic sequence's deferred call).
func walkDeferInDefer() int {
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r += 10
			}
		}()
		defer func() {
			defer func() {
				if recover() != nil {
					r += 1
				}
			}()
		}()
		panic("x")
	}()
	return r
}

// recover() in a GOROUTINE spawned by the deferred function: a different
// goroutine, no panic to recover (nil); the deferred function then recovers
// its own.
func walkRecoverInSpawnedGoroutine() int {
	res := 0
	func() {
		defer func() {
			done := make(chan int)
			go func() {
				if recover() == nil {
					done <- 1
				} else {
					done <- 2
				}
			}()
			res = <-done
			if recover() != nil {
				res += 10
			}
		}()
		panic("x")
	}()
	return res
}

type rec struct{ hit *int }

func (r rec) Rec() {
	if recover() != nil {
		*r.hit = 1
	}
}

// A deferred METHOD EXPRESSION `defer rec.Rec(v)`: the method is the deferred
// function and its recover() applies.
func walkDeferMethodExpr() int {
	hit := 0
	func() {
		defer rec.Rec(rec{&hit})
		panic("x")
	}()
	return hit
}

func genericRec[T any](p *T, v T) {
	if recover() != nil {
		*p = v
	}
}

// A deferred GENERIC function instantiation recovers.
func walkDeferGeneric() int {
	hit := 0
	func() {
		defer genericRec(&hit, 7)
		panic("x")
	}()
	return hit
}

func main() {}
