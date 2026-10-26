package main

// panic(nil) under the Go 1.21+ default is a *runtime.PanicNilError (recover() != nil);
// a `godebug panicnil=1` line restores the pre-1.21 behaviour (recover() == nil). gc reads
// such a line from go.mod (BUG-128: the frontend refuses it there by name) AND from go.work,
// which applies to the workspace's main modules — the frontend does not read go.work.
func probe() (r bool) {
	defer func() { r = recover() == nil }()
	panic(nil)
}

func main() { println(probe()) }
