package main

func panicNilRecover() (result int) {
	// Pinned behavior (2026-07-30 audit correction): under the oracle's
	// GOPATH-mode invocation (GO111MODULE=off, no go.mod) Go keeps the
	// LEGACY panic(nil) semantics — recover() returns nil, the guard does
	// not fire, and result stays 0. panicPayload's docstring in
	// GoLean/GoCore/Machine.lean records the module-mode (Go 1.21+
	// PanicNilError) knob that would flip this case.
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
