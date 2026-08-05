package main

// Unrecovered panic(nil) under the MODERN semantics (GODEBUG=panicnil=0
// oracle; arc-final audit F21): the abort line is the PanicNilError
// message, not "nil".
func panicNilAbort() {
	panic(nil)
}

func main() {
	panicNilAbort()
}
