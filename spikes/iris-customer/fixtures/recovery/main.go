package main

func fail() { panic("customer panic") }

// A defer captures the named result's location. Recovery changes both the
// panic continuation and the observable result stored at that location.
func Recovered() (result bool) {
	defer func() {
		if recover() != nil {
			result = true
		}
	}()
	fail()
	return false
}

func Normal() (result bool) {
	result = true
	return
}

func Uncaught() { fail() }
