package main

// Sweep S12 (panic and recover: payload, abort text, the recover walk) —
// the ABORT LINE for every basic payload kind `runtime/error.go`
// printpanicval prints as it is (the matrix's A cells; lane
// sweep/s12-panic-recover, 2026-10-27). gc prints integer kinds in decimal,
// bools as `true`/`false`, a string's raw bytes; a nil interface — from a
// literal, a variable or a call result — is the Go 1.21+ `*runtime.PanicNilError`
// (BUG-150's rule). The machine's arms are `renderPanicPayload` (Machine.lean).

type code int

func abortStringComputed(a int, b int) {
	s := "computed-"
	if a > b {
		s += "gt"
	} else {
		s += "le"
	}
	panic(s)
}

// The empty string: gc writes `panic: ` and nothing else on the line; the
// output prefix makes the row's reason non-empty.
func abortStringEmpty() {
	print("empty-payload\n")
	panic("")
}

func abortInt8() { panic(int8(-3)) }

func abortInt16() { panic(int16(-300)) }

func abortRune() { panic('x') }

func abortInt64Min() { panic(int64(-9223372036854775808)) }

func abortUint() { panic(uint(7)) }

func abortByte() { panic(byte(200)) }

func abortUint16() { panic(uint16(65535)) }

func abortUint32() { panic(uint32(4294967295)) }

func abortUint64Max() { panic(uint64(18446744073709551615)) }

func abortUintptr() { panic(uintptr(4096)) }

func abortBoolFalse() { panic(false) }

func abortNilErrorVar() {
	var e error
	panic(e)
}

func nilError() error { return nil }

func abortNilFromResult() { panic(nilError()) }

func genericPanic[T any](v T) { panic(v) }

func abortGenericInt() { genericPanic(3) }

func abortGenericDefined() { genericPanic(code(3)) }

func abortAnyVarInt() {
	var x any = 3
	panic(x)
}

func main() {}
