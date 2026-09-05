package main

// R3/R20 probes: what reaches an observable text or the observation
// channel when a RECOVERED runtime error's dynamic type is named.
func boom() { var s []int; _ = s[3] }

// (a) concrete-target assert on the recovered payload: gc names the
// concrete runtime type in the panic text.
func assertRecoveredToInt() int {
	defer func() {
		r := recover()
		_ = r.(int) // gc: interface conversion: interface {} is runtime.boundsError, not int
	}()
	boom()
	return 0
}

// (b) the recovered payload returned as `any` — the observation channel
// renders its dynamic type (reflect Name()).
func recoveredAsAny() (out any) {
	defer func() { out = recover() }()
	boom()
	return nil
}

// (c) r.(error).Error() — the BUG-009/BUG-053 refusal path.
func recoveredErrorText() (out string) {
	defer func() { out = recover().(error).Error() }()
	boom()
	return ""
}

func main() {
	println(recoveredErrorText())
	func() { defer func() { println(recover().(error).Error()) }(); assertRecoveredToInt() }()
	println(recoveredAsAny() != nil)
}
