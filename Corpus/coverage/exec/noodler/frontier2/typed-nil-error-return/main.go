// noodler frontier probe — typed nil *T returned as error is a non-nil interface
package main

type MyErr struct{}

func (*MyErr) Error() string { return "myerr" }

func mayFail(fail bool) error {
	var p *MyErr
	if fail {
		p = &MyErr{}
	}
	return p
}

// Returning a typed nil pointer as error yields a NON-nil error.
func typedNilErrorReturn() (bool, bool) {
	e1 := mayFail(false)
	e2 := mayFail(true)
	return e1 != nil, e2 != nil && e2.Error() == "myerr"
}

func main() {}
