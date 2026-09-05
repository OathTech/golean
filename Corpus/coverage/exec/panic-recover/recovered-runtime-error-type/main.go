// The DYNAMIC TYPE of a recovered runtime error (lane fr19-bug097, audit
// fix round R3/R20, 2026-09-05). gc's runtime panics carry CONCRETE types
// — `runtime.boundsError` (index), `runtime.errorString` (nil deref),
// `*runtime.TypeAssertionError`, `runtime.runtimeError` (divide) — while
// the machine mints ONE synthetic id (`$runtime.Error`, GoCore/Syntax.lean)
// for every runtime fault. Two channels can name that type:
//   - the observation channel (reflect `Name()` of a returned `any`):
//     gc `boundsError`; the machine's `TypeId.unqualified` spelled `Error`
//     — a WRONG observation, measured `.tmp/fix/probe-r3` (BUG-099);
//   - a concrete-target assert's panic text: gc `interface conversion:
//     interface {} is runtime.boundsError, not int`; the machine REFUSES
//     by name (no byte-exact text exists) — a designed red.
package main

func boom() {
	var s []int
	_ = s[3]
}

// gc observation: {"dynamic":"boundsError", ...}
func recoveredRuntimeErrorAsAny() (out any) {
	defer func() { out = recover() }()
	boom()
	return nil
}

// gc: interface conversion: interface {} is runtime.boundsError, not int
func recoveredRuntimeErrorAssertInt() int {
	defer func() {
		r := recover()
		_ = r.(int)
	}()
	boom()
	return 0
}

func main() {}
