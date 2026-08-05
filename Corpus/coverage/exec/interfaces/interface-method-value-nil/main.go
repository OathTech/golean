package main

// An interface METHOD VALUE from a nil interface panics AT CREATION (the
// itab load) with Go's nil dereference — NOT at the later call. `created`
// pins the moment: it stays 0, so the recovered result is 2. (The
// differential caught the first lowering capturing the nil box and
// panicking at call time: Lean 12 vs Go 2.)

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
