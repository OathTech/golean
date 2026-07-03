package main

type errorCode int

func (e errorCode) Error() string {
	if e == 1 {
		return "one"
	}
	return "other"
}

func nilErrorReturnIsNil() int {
	var err error
	if err == nil {
		return 1
	}
	return 0
}

func errorValueEquality() int {
	var a error = errorCode(1)
	var b error = errorCode(1)
	var c error = errorCode(2)
	score := 0
	if a == b {
		score += 10
	}
	if a != c {
		score += 1
	}
	return score
}

type pointerError struct {
	n int
}

func (e *pointerError) Error() string {
	return "ptr"
}

func errorPointerIdentity() int {
	p := &pointerError{n: 1}
	var a error = p
	var b error = p
	var c error = &pointerError{n: 1}
	score := 0
	if a == b {
		score += 10
	}
	if a != c {
		score += 1
	}
	return score
}

type sliceError struct {
	xs []int
}

func (e sliceError) Error() string {
	return "slice"
}

func errorUncomparableComparePanic() int {
	var err error = sliceError{xs: []int{1}}
	if err == err {
		return 1
	}
	return 0
}

type temporaryError interface {
	error
	Temporary() bool
}

type retryError struct {
	retry bool
}

func (e retryError) Error() string {
	return "retry"
}

func (e retryError) Temporary() bool {
	return e.retry
}

func errorExtraInterfaceAssertion() int {
	var err error = retryError{retry: true}
	x, ok := err.(temporaryError)
	if ok && x.Temporary() {
		return len(x.Error())
	}
	return 0
}

type baseError struct {
	msg string
}

func (e baseError) Error() string {
	return e.msg
}

type wrappedEmbeddedError struct {
	baseError
}

func errorPromotedMethod() int {
	var err error = wrappedEmbeddedError{
		baseError: baseError{msg: "wrapped"},
	}
	return len(err.Error())
}

type nilReceiverError struct {
	msg string
}

func (e *nilReceiverError) Error() string {
	if e == nil {
		return "nil"
	}
	return e.msg
}

func nilPointerErrorMethodCall() int {
	var p *nilReceiverError
	var err error = p
	if err == nil {
		return 0
	}
	return len(err.Error())
}

func errorInAnyRoundTrip() int {
	var err error = errorCode(1)
	var x any = err
	y, ok := x.(error)
	if !ok {
		return 0
	}
	return len(y.Error())
}
