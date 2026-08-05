package main

// An interface METHOD VALUE from a nil interface: creation does NOT panic
// (the box is merely captured); the CALL panics with Go's nil dereference.
// `created` proves the creation moment passed.

type nilMVIface interface {
	m() int
}

func interfaceMethodValueNil() (r int) {
	created := 0
	defer func() {
		if recover() != nil {
			r = created*10 + 2
		}
	}()
	var x nilMVIface
	f := x.m
	created = 1
	return f()
}
