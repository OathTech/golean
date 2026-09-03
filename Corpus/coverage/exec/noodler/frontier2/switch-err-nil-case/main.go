// noodler frontier probe — expression switch on an error with case nil
package main

import "errors"

func op(n int) error {
	if n < 0 {
		return errors.New("neg")
	}
	return nil
}

// switch on an error value with case nil.
func switchErrNilCase() (int, int) {
	f := func(n int) int {
		switch err := op(n); err {
		case nil:
			return 1
		default:
			return len(err.Error())
		}
	}
	return f(1), f(-1)
}

func main() {}
