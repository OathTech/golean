package main

func panicNilRecover() (result int) {
	// MODERN (Go 1.21+) panic(nil) semantics (arc-final audit F21,
	// 2026-08-06): panic(nil) delivers *runtime.PanicNilError, so
	// recover() is guaranteed non-nil and the guard fires — result 1.
	// The oracle runs with GODEBUG=panicnil=0 (scripts/diff-coverage
	// go_run_oracle): GOPATH mode otherwise keeps the LEGACY behavior
	// (recover() returns nil, result 0), which the model matched before
	// only by that config coincidence (unwinding arc §A2; the old pinned
	// answer was 0).
	defer func() {
		if recover() != nil {
			result = 1
		}
	}()
	panic(nil)
}

func main() {
	panicNilRecover()
}
