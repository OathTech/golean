//go:debug panicnil=1
package main

// Under the legacy setting panic(nil) is recovered as a nil value, so
// recover() == nil is true; under the Go 1.21+ default (and in the model)
// it is *runtime.PanicNilError, false.
func recoverNilIsNil() (r bool) {
	defer func() { r = recover() == nil }()
	panic(nil)
}

func debugPanicNil() bool { return recoverNilIsNil() }

func main() { println(debugPanicNil()) }
