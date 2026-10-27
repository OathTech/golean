package main

import (
	"errors"
	"fmt"
)

// Sweep S12 — the failed-assertion text NAMES the recovered payload's
// dynamic type (matrix cells C01–C11, C13, C14, C16; lane
// sweep/s12-panic-recover, 2026-10-27): `r.(int)` on the value `recover()`
// returned panics with gc's `interface conversion: interface {} is <dyn>,
// not int` (runtime/error.go TypeAssertionError.Error), so the text is a
// second channel on the payload's dynamic type beside the assert-back rows.
// The machine: `typeAssertPanicMessage` / `goTypeNameForMessage` (Ops.lean);
// a stdlib error's type prints its package-qualified name.

func catch(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

type plain struct{ x int }

type defStr string

func assertFailString() int {
	r := catch(func() { panic("s") })
	return r.(int)
}

func assertFailFloat() int {
	r := catch(func() { panic(1.5) })
	return r.(int)
}

func assertFailSlice() int {
	r := catch(func() { panic([]int{1}) })
	return r.(int)
}

func assertFailMap() int {
	r := catch(func() { panic(map[string]int{}) })
	return r.(int)
}

func assertFailFunc() int {
	r := catch(func() { panic(func() {}) })
	return r.(int)
}

func assertFailChan() int {
	r := catch(func() { panic(make(chan int)) })
	return r.(int)
}

func assertFailPointer() plain {
	r := catch(func() { panic(&plain{1}) })
	return r.(plain)
}

func assertFailArray() int {
	r := catch(func() { panic([2]int{1, 2}) })
	return r.(int)
}

func assertFailDefinedString() string {
	r := catch(func() { panic(defStr("x")) })
	return r.(string)
}

func assertFailErrorsNew() int {
	r := catch(func() { panic(errors.New("e")) })
	return r.(int)
}

func assertFailFmtErrorf() int {
	r := catch(func() { panic(fmt.Errorf("e-%d", 1)) })
	return r.(int)
}

func assertFailBool() int {
	r := catch(func() { panic(true) })
	return r.(int)
}

func assertFailInt8() int {
	r := catch(func() { panic(int8(1)) })
	return r.(int)
}

func assertFailStruct() int {
	r := catch(func() { panic(plain{1}) })
	return r.(int)
}

// A TypeAssertionError recovered, then a DIFFERENT panic: the head line is
// the runtime error's text with ` [recovered]`.
func repanicAssertFail() {
	defer func() {
		_ = recover()
		panic("other")
	}()
	var x any = "s"
	_ = x.(int)
}

func main() {}
