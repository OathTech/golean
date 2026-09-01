package main

// RED BY DESIGN (BUG-078, $GOROOT/test harvest 2026-09-01,
// issue34395.go): array types past the interpreter's materialization
// budget (1<<20 elements, GoLean/NativeToIR.lean arrayLenBudget)
// refuse BY NAME at the wire boundary instead of grinding the
// quadratic element-wise normalize path to a native stack overflow
// (exit 134 — a process abort is not a cause-naming refusal). The
// expected column records the oracle's truth: gc materializes the
// 2 MiB array fine and reads back the 42.
var big = [2 * 1024 * 1024]byte{42}

func arrayOverBudget() int {
	if big[0] != 42 {
		panic("bad")
	}
	return 1
}
