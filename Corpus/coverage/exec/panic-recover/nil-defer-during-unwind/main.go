package main

// Pins Step.panicFrameDeferNil's recovering path (2026-07-30 pre-merge
// audit: the rule was validated only by reading): a nil deferred callee
// invoked WHILE a panic is already unwinding appends its nil-dereference
// panic to the in-flight chain (newest last), and the outer deferred
// recover() sees that runtime error — recovering it cancels the whole
// unwind, so the function returns normally with r = 1.
func nilDeferDuringUnwind() (r int) {
	defer func() {
		if recover() != nil {
			r = 1
		}
	}()
	var g func()
	defer g()
	panic("boom")
}
