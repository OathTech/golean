package main

import (
	"errors"
	"fmt"
)

// Sweep S12 — the RECOVERED payload keeps its dynamic type and value
// (matrix cells B03–B05, B10–B15, B17–B20, B22–B24; lane
// sweep/s12-panic-recover, 2026-10-27): `recover()` returns the interface
// value passed to `panic` (spec#Handling_panics), asserted back at its own
// type and rejected at every other. Each subject returns a small code whose
// digits are the checks that held. The machine: `recoverResult` /
// `recoverAtDeferred`, the payload untouched by `panicPayload`.

func catch(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

func recoverInt8() int {
	r := catch(func() { panic(int8(-5)) })
	v, ok := r.(int8)
	_, asInt := r.(int)
	_, asU8 := r.(uint8)
	c := 0
	if ok && v == -5 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	if !asU8 {
		c += 100
	}
	return c
}

func recoverInt16() int {
	r := catch(func() { panic(int16(-300)) })
	v, ok := r.(int16)
	_, asInt := r.(int)
	c := 0
	if ok && v == -300 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

func recoverInt32() int {
	r := catch(func() { panic('x') })
	v, ok := r.(rune)
	_, asInt := r.(int)
	c := 0
	if ok && v == 120 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

func recoverInt64() int {
	r := catch(func() { panic(int64(1) << 40) })
	v, ok := r.(int64)
	_, asInt := r.(int)
	c := 0
	if ok && v == 1<<40 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

func recoverUint() int {
	r := catch(func() { panic(uint(7)) })
	v, ok := r.(uint)
	_, asInt := r.(int)
	c := 0
	if ok && v == 7 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

func recoverUint8() int {
	r := catch(func() { panic(byte(200)) })
	v, ok := r.(uint8)
	_, asInt := r.(int)
	_, asI8 := r.(int8)
	c := 0
	if ok && v == 200 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	if !asI8 {
		c += 100
	}
	return c
}

func recoverUint16() int {
	r := catch(func() { panic(uint16(65535)) })
	v, ok := r.(uint16)
	_, asInt := r.(int)
	c := 0
	if ok && v == 65535 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

func recoverUint32() int {
	r := catch(func() { panic(uint32(4294967295)) })
	v, ok := r.(uint32)
	_, asInt := r.(int)
	c := 0
	if ok && v == 4294967295 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

func recoverUint64() int {
	r := catch(func() { panic(uint64(18446744073709551615)) })
	v, ok := r.(uint64)
	_, asInt := r.(int)
	c := 0
	if ok && v == 18446744073709551615 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

func recoverUintptr() int {
	r := catch(func() { panic(uintptr(4096)) })
	v, ok := r.(uintptr)
	_, asUint := r.(uint)
	c := 0
	if ok && v == 4096 {
		c += 1
	}
	if !asUint {
		c += 10
	}
	return c
}

func recoverFloat64() int {
	r := catch(func() { panic(2.5) })
	v, ok := r.(float64)
	_, asF32 := r.(float32)
	_, asInt := r.(int)
	c := 0
	if ok && v == 2.5 {
		c += 1
	}
	if !asF32 {
		c += 10
	}
	if !asInt {
		c += 100
	}
	return c
}

func recoverFloat32() int {
	r := catch(func() { panic(float32(0.25)) })
	v, ok := r.(float32)
	_, asF64 := r.(float64)
	c := 0
	if ok && v == 0.25 {
		c += 1
	}
	if !asF64 {
		c += 10
	}
	return c
}

func recoverBool() int {
	r := catch(func() { panic(true) })
	v, ok := r.(bool)
	_, asInt := r.(int)
	c := 0
	if ok && v {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

// A recovered slice ALIASES the panicked one.
func recoverSlice() int {
	s := []int{1, 2, 3}
	r := catch(func() { panic(s) })
	t, ok := r.([]int)
	if !ok {
		return -1
	}
	t[0] = 9
	return s[0]*100 + len(t)*10 + cap(t)
}

// A recovered map is the same map.
func recoverMap() int {
	m := map[string]int{"a": 1}
	r := catch(func() { panic(m) })
	n, ok := r.(map[string]int)
	if !ok {
		return -1
	}
	n["b"] = 5
	return m["b"]*10 + len(m)
}

// A recovered func value is callable.
func recoverFunc() int {
	r := catch(func() { panic(func() int { return 41 }) })
	f, ok := r.(func() int)
	if !ok {
		return -1
	}
	return f() + 1
}

// A recovered channel is the same channel.
func recoverChan() int {
	ch := make(chan int, 1)
	r := catch(func() { panic(ch) })
	c, ok := r.(chan int)
	if !ok {
		return -1
	}
	c <- 3
	return <-ch
}

// A recovered array is a COPY (value semantics through the box).
func recoverArray() int {
	a := [2]int{1, 2}
	r := catch(func() { panic(a) })
	b, ok := r.([2]int)
	if !ok {
		return -1
	}
	b[0] = 9
	return a[0]*10 + b[0]
}

type defInt int

type defStr string

type defStruct struct{ x int }

func recoverDefinedInt() int {
	r := catch(func() { panic(defInt(5)) })
	v, ok := r.(defInt)
	_, asInt := r.(int)
	c := 0
	if ok && v == 5 {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

func recoverDefinedString() int {
	r := catch(func() { panic(defStr("v")) })
	v, ok := r.(defStr)
	_, asStr := r.(string)
	c := 0
	if ok && v == "v" {
		c += 1
	}
	if !asStr {
		c += 10
	}
	return c
}

func recoverDefinedStruct() int {
	r := catch(func() { panic(defStruct{7}) })
	v, ok := r.(defStruct)
	_, asPtr := r.(*defStruct)
	c := 0
	if ok && v.x == 7 {
		c += 1
	}
	if !asPtr {
		c += 10
	}
	return c
}

var sentinel = errors.New("sentinel-text")

// errors.New: the recovered error IS the sentinel (identity) and keeps its text.
func recoverErrorsNewIdentity() int {
	r := catch(func() { panic(sentinel) })
	e, ok := r.(error)
	c := 0
	if ok && e == sentinel {
		c += 1
	}
	if ok && e.Error() == "sentinel-text" {
		c += 10
	}
	if _, isStr := r.(string); !isStr {
		c += 100
	}
	return c
}

func recoverFmtErrorf() int {
	r := catch(func() { panic(fmt.Errorf("fmt-%d", 7)) })
	e, ok := r.(error)
	c := 0
	if ok && e.Error() == "fmt-7" {
		c += 1
	}
	if _, isStr := r.(string); !isStr {
		c += 10
	}
	return c
}

type wrapErr struct {
	op    string
	inner error
}

func (w *wrapErr) Error() string { return w.op + ": " + w.inner.Error() }

func (w *wrapErr) Unwrap() error { return w.inner }

// errors.Unwrap on the recovered wrapper reaches the inner sentinel.
func recoverUnwrap() int {
	r := catch(func() { panic(&wrapErr{"open", sentinel}) })
	e, ok := r.(error)
	c := 0
	if ok && e.Error() == "open: sentinel-text" {
		c += 1
	}
	if ok && errors.Unwrap(e) == sentinel {
		c += 10
	}
	return c
}

// A recovered RUNTIME error is not a string (the comma-ok false half of
// BUG-099's observation; the positive `r.(error)` half refuses there).
func recoverRuntimeErrorNotString() int {
	r := catch(func() {
		var s []int
		_ = s[3]
	})
	c := 0
	if r != nil {
		c += 1
	}
	if _, isStr := r.(string); !isStr {
		c += 10
	}
	if _, isInt := r.(int); !isInt {
		c += 100
	}
	return c
}

func genericRecover[T any](v T) (ok bool) {
	defer func() { _, ok = recover().(T) }()
	panic(v)
}

func recoverGenericAssert() int {
	c := 0
	if genericRecover(3) {
		c += 1
	}
	if genericRecover("s") {
		c += 10
	}
	if genericRecover(defInt(2)) {
		c += 100
	}
	return c
}

type empty struct{}

func recoverEmptyStruct() int {
	r := catch(func() { panic(empty{}) })
	_, ok := r.(empty)
	_, asInt := r.(int)
	c := 0
	if ok {
		c += 1
	}
	if !asInt {
		c += 10
	}
	return c
}

type ptrErr struct{ m string }

func (e *ptrErr) Error() string { return e.m }

// A pointer boxed in an error-typed variable is recovered as the pointer.
func recoverPtrThroughError() int {
	var e error = &ptrErr{"m"}
	r := catch(func() { panic(e) })
	p, ok := r.(*ptrErr)
	c := 0
	if ok && p.m == "m" {
		c += 1
	}
	if e2, isErr := r.(error); isErr && e2 == e {
		c += 10
	}
	return c
}

func main() {}
