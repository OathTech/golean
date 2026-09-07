package main

func flip(b bool) (result bool) {
	return !b
}

// This ordinary call is deliberately one frame away from a deferred handler.
func indirectRecover() (result bool) {
	return recover() == nil
}

// Both handlers capture the same result root. Reversing their registration
// order changes the result: the last handler recovers and assigns true, then
// the first handler negates that shared cell using an ordinary helper call.
func Shared(b bool) (result bool) {
	defer func() {
		result = flip(result)
	}()
	defer func() {
		// Run while a panic may still be active. An indirect recover must not
		// consume that panic before the following direct recover sees it.
		outside := indirectRecover()
		if recover() != nil {
			result = outside
		}
	}()
	// Normal completion leaves false for the first handler to negate;
	// recovered completion writes true first. The final result is !b.
	result = flip(true)
	if b {
		panic("shared recovery")
	}
	return
}

// The valid Go expression is admitted outside any deferred handler too.
func Outside() (result bool) {
	return recover() == nil
}

// The differential harness currently accepts integer external arguments;
// these wrappers exercise both Boolean inputs of the same checked body.
func SharedFalse() (result bool) { return Shared(false) }
func SharedTrue() (result bool)  { return Shared(true) }

// A semantic control: swapping registration order changes the recovered
// result from false to true. Both handlers still share exactly one cell.
func Reversed(b bool) (result bool) {
	defer func() {
		outside := indirectRecover()
		if recover() != nil {
			result = outside
		}
	}()
	defer func() {
		result = flip(result)
	}()
	result = flip(true)
	if b {
		panic("shared recovery")
	}
	return
}

// Another semantic control: inlining the helper's recover makes it direct.
// It now consumes the panic; the second recover observes nil, so this differs
// from Shared(true). Treating an indirect recovery as effective is detectable.
func DirectRecoveryControl(b bool) (result bool) {
	defer func() {
		result = flip(result)
	}()
	defer func() {
		outside := recover() == nil
		if recover() != nil {
			result = outside
		}
	}()
	result = flip(true)
	if b {
		panic("shared recovery")
	}
	return
}

func ReversedTrue() (result bool) { return Reversed(true) }
func DirectTrue() (result bool)   { return DirectRecoveryControl(true) }
