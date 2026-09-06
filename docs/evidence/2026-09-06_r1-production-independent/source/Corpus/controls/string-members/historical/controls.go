package main

// These concrete controls deliberately use more of Go than the O2 static
// profile (string equality, type assertions, and integer order encoding).
// The checked subject artifact is the separate original package. Its
// definitions are copied here exactly, never replaced by control mocks.
func catchEqual() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "orig"
	}()
	Equal()
	return false
}

func catchUnequal() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "next"
	}()
	Unequal()
	return false
}

func catchMultiple() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "third"
	}()
	Multiple()
	return false
}

func ControlInvalidBefore() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "\xff\x00\\\nZ"
	}()
	InvalidBefore()
	return false
}

func ControlInvalidAfter() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "a\n\xff"
	}()
	InvalidAfter()
	return false
}

func ControlDynamic() bool {
	return catchHistorical() && catchEqual() && catchUnequal() && catchMultiple() &&
		ControlInvalidBefore() && ControlInvalidAfter() && catchRethrow() && catchComputed() &&
		catchUnicode() && catchControls() && controlRecoveredBytes()
}

func catchUnicode() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "界🙂"
	}()
	Unicode()
	return false
}

func catchControls() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "a\x00\x01\t\r\nZ"
	}()
	Controls()
	return false
}

// Paired control for InvalidRecovered: the first handler checks the exact
// value it recovered before the same explicit "orig" replacement panic;
// the outer handler checks that the replacement really remained active.
func controlRecoveredBytes() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = result && ok && value == "orig"
	}()
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "\xff\x00\\\nZ"
		panic("orig")
	}()
	panic("\xff\x00\\\nZ")
}

func ControlRethrow() {
	defer func() { panic(recover()) }()
	panic("orig")
}

// Runtime concatenation exercises the other concrete equal-string boxing
// path. Equality of values does not assert interface data-pointer identity.
//
//go:noinline
func computedEqual(left, right string) string { return left + right }

func ControlComputed() {
	defer func() {
		_ = recover()
		panic(computedEqual("ori", "g"))
	}()
	panic("orig")
}

func catchRethrow() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "orig"
	}()
	ControlRethrow()
	return false
}

func catchComputed() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "orig"
	}()
	ControlComputed()
	return false
}

func ControlNormal() bool {
	return Normal()
}

func ControlDirect() (result bool) {
	defer func() { result = recover() != nil }()
	panic("direct")
}

func indirectRecovery() any {
	return recover()
}

func ControlIndirect() (result bool) {
	defer func() { result = recover() != nil && result }()
	defer func() { result = indirectRecovery() == nil }()
	panic("indirect")
}

func ControlOrder() (result int) {
	defer func() { result = result*10 + 1 }()
	defer func() { result = result*10 + 2 }()
	return 0
}

func ControlReversed() (result int) {
	defer func() { result = result*10 + 2 }()
	defer func() { result = result*10 + 1 }()
	return 0
}

func catchHistorical() (result bool) {
	defer func() {
		value, ok := recover().(string)
		result = ok && value == "orig"
	}()
	repanicSameValueAbort()
	return false
}
