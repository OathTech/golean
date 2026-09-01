package main

// The CONVERSION form of nil-to-interface (and nil-to-func) —
// `error(nil)`, `any(nil)`, `(func())(nil)` — is legal Go
// (spec#Conversions + spec#Assignability: nil is assignable/convertible
// to interface, function, pointer, slice, map and channel types) and
// yields the type's zero value. BUG-077 ($GOROOT/test harvest
// 2026-09-01: issue19911.go, issue53619.go, typeparam/issue42758.go
// refused): the machine's nil-literal arm enumerated the nilable types
// without interface/func arms, so the typed nil wire node the
// conversion form carries was refused where the (untyped) assignment
// form lowered.

type errNilET struct{}

func (*errNilET) Error() string { return "err" }

// issue19911 shape: error(nil) is THE nil interface.
func convErrorNilIsNil() int {
	if error(nil) == nil {
		return 1
	}
	return 0
}

func convAnyNilIsNil() int {
	if any(nil) == nil {
		return 1
	}
	return 0
}

// issue19911 core: a typed-nil pointer boxed into error is NOT the
// nil interface produced by error(nil).
func convTypedNilVsErrorNil() int {
	r := 0
	if (*errNilET)(nil) == error(nil) {
		r += 1
	}
	nilET := (*errNilET)(nil)
	nilError := error(nil)
	if nilET != nilError {
		r += 2
	}
	return r
}

// The func-type conversion sibling: (func())(nil) is the nil func value.
func convFuncNilIsNil() int {
	if (func())(nil) == nil {
		return 1
	}
	return 0
}
