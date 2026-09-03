// noodler frontier probe — recover() writing a named error result
package main

import "errors"

func risky(n int) (res int, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = errors.New("recovered")
			res = -1
		}
	}()
	s := []int{1, 2}
	return s[n], nil
}

// The recover-into-named-error idiom.
func recoverIntoNamedError() (int, string, bool) {
	a, e1 := risky(1)
	b, e2 := risky(5)
	return a + b, e2.Error(), e1 == nil
}

func main() {}
