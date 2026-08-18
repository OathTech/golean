// spec#Handling_panics block Handling_panics-2-e7d4cef6
// The spec's three example panic calls — panic(42),
// panic("unreachable"), panic(Error("cannot parse")) — each recovered
// by a deferred function, pinning that the recovered interface value
// is EXACTLY the value passed to panic (dynamic type and value). The
// spec leaves Error undeclared; here it is a defined string type
// implementing error, matching the surrounding prose's
// "program-defined error conditions".
package main

type Error string

func (e Error) Error() string { return string(e) }

func panicInt() (result int) {
	defer func() {
		if x := recover(); x != nil {
			if v, ok := x.(int); ok && v == 42 {
				result = 1
			}
		}
	}()
	panic(42)
}

func panicString() (result int) {
	defer func() {
		if x := recover(); x != nil {
			if s, ok := x.(string); ok && s == "unreachable" {
				result = 1
			}
		}
	}()
	panic("unreachable")
}

func panicErrorValue() (result int) {
	defer func() {
		if x := recover(); x != nil {
			if e, ok := x.(error); ok && e.Error() == "cannot parse" {
				result = 1
			}
		}
	}()
	panic(Error("cannot parse"))
}

func main() {
	panicInt()
}
