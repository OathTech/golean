package main

// Round-4 pins (BUG-038): storing through a NIL pointer-to-array
// element is gc's recoverable nil-pointer-dereference panic — at the
// STORE (phase 2), after earlier stores landed. The index-target
// machinery's missing nil-base arm reports a wrongly-stuck run
// instead.

func naRecover(fn func()) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	fn()
	return 0
}

func nilArrayElemStore() int {
	var bp *[3]int
	return naRecover(func() { (*bp)[0] = 1 })
}

func nilArrayElemStoreSecond() int {
	var bp *[3]int
	x := 0
	hit := naRecover(func() { x, (*bp)[0] = 1, 7 })
	return hit*100 + x*5
}

func main() {
	nilArrayElemStore()
}
