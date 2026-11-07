package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07), the train-31 pre-merge audit's finding 5: a PARENTHESISED
// fmt callee, `(fmt.Sprint)(1, 2)`. The emitter desugars it as the call it is (the S28 lane's unparen
// rule), but the shim-injection scans read the bare `call.Fun`, so the dyn shim was not injected and the
// desugar refused naming an apparatus inconsistency («shim … not injected»). Both scans now read the
// callee through its parentheses; gc `1 2`, the machine the same.

import "fmt"

func parenSprint() string  { return (fmt.Sprint)(1, 2) }
func parenSprintf() string { return (fmt.Sprintf)("%d-%s", 1, "a") + (fmt.Sprintln)(2, 3) }
func parenSpread() string  { a := []any{1, "x"}; return (fmt.Sprint)(a...) }

func main() { print(parenSprint(), parenSprintf(), parenSpread()) }
