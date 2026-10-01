package main

// The `rand-intn` PRIMITIVE (window unit 5b, 2026-09-30): the `[0, n)` DRAW of
// `math/rand.Intn(n)` and `math/rand/v2.IntN(n)` — the package-level
// functions — lowers to ONE machine statement, `Stmt.randIntn` (GoLean/GoCore/
// Syntax.lean, whose docstring is the envelope statement of the choice site
// `ChoiceSite.intn`: bound `n` exactly, every value of `[0, n)` a member, `n = 1`
// a no-pop consult). ADMITTED [USER] Mike 2026-09-30 (item 2 of «The raft-proofs
// team's subject-delta note (2026-09-30) — RULED», relayed by the [AGENT]
// coordinator — cite as relayed: a native `Intn`-style pick site, GENERAL — «a
// value in `[0, n)`, panic if `n ≤ 0`», not raft-specific); design
// docs/2026-09-30_intn-pick-design.md. Counted as the THIRD of the register's
// library-origin primitives (stdlibregister.go; the cap 2 -> 3 is posed there).
//
// Why a primitive and not source-through: the draw IS nondeterminism — the
// weakest machine admits every value of `[0, n)`, so the semantics is the
// ENVELOPE, reified on the choice tape, never a modeled generator (`math/rand`'s
// PCG/ChaCha8 state and `runtime.rand` seeding are exactly what the doctrine
// declines to model). What the LANGUAGE has: the callee's `n <= 0` guard,
// `if n <= 0 { panic("invalid argument to Intn") }` (deps/go/src/math/rand/
// rand.go:179-181 @ go1.26.5; IntN: `invalid argument to IntN`, math/rand/v2/
// rand.go:192-193 — file:line citations because neither package is
// source-through, the float-bits convention). That guard is a plain
// `panic(string)` — a payload class a machine apply's `.panic` could NOT
// deliver (`deliver` boxes those as `runtime.Error`) — so the DECODER expands
// the node as `$intn := n; if $intn < 1 { panic("<text>") }; randIntn target $intn`
// (GoLean/NativeToIR.lean `expandRandIntn`): upstream's own guard, then the
// draw, whose machine domain is `n >= 1` (a bypass is `stuck` by name). The
// wire node names the CALLEE (`Intn` / `IntN`) so the decoder chooses the text
// from a closed table; a forged tag refuses by name.
//
// The lowering is an EFFECTFUL node (the effect flag is `true`, like `sync-op`
// / `atomic-op`): the caller hoists it into a fresh temp exactly like a call,
// and the decoder admits it only where it admits `call` (an expression
// statement; the single RHS of an assignment). The pinned signature
// (`func(int) int`, package-level, no receiver) is re-checked at every call, so
// a toolchain whose `math/rand` differs from the pin refuses rather than
// lowering a different function.
//
// NOT bound (they keep the by-name package quarantine `package-selector call
// … (package "math/rand" surface not modeled)`): the METHOD forms
// `(*rand.Rand).Intn` / `(*rand.Rand).IntN` — a `*Rand` value needs `rand.New`
// / `NewSource`, outside the modeled surface, and a nil `*Rand` dereferences
// inside gc, so binding the method without modelling the receiver would be a
// wrong answer; every other member of the two packages (`Int63n`, `Int31n`,
// `Perm`, `Shuffle`, `Float64`, `Seed`, …: other contracts). A `defer` / `go`
// of the function refuses by name (`refuseRandIntnDeferGo`): as a FUNCTION
// VALUE the callee has no lowering, and the draw is defined at direct-call
// sites only.

import (
	"go/ast"
	"go/types"
)

// randIntnCallees: the wire callee tag per admitted (package path, function
// name). The tag selects the guard TEXT in the decoder's closed table.
var randIntnCallees = map[[2]string]string{
	{"math/rand", "Intn"}:    "Intn",
	{"math/rand/v2", "IntN"}: "IntN",
}

// isRandIntnFunc reports whether obj is one of the two admitted package-level
// draw functions (methods never route here: `sig.Recv() != nil` is refused).
func isRandIntnFunc(obj types.Object) (*types.Func, string, bool) {
	fn, ok := obj.(*types.Func)
	if !ok || fn.Pkg() == nil {
		return nil, "", false
	}
	tag, listed := randIntnCallees[[2]string{fn.Pkg().Path(), fn.Name()}]
	if !listed {
		return nil, "", false
	}
	sig, ok := fn.Type().(*types.Signature)
	if !ok || sig.Recv() != nil {
		return nil, "", false
	}
	return fn, tag, true
}

// emitRandIntnCall lowers a direct call of `math/rand.Intn` / `math/rand/v2.IntN`
// to the `rand-intn` expression node. The signature is checked against the pin
// (one `int` parameter, one `int` result); any drift refuses by name.
func (e *emitter) emitRandIntnCall(c *ast.CallExpr, fn *types.Func, tag string) (any, bool, error) {
	sig, _ := fn.Type().(*types.Signature)
	if sig == nil || sig.Params().Len() != 1 || sig.Results().Len() != 1 || sig.Variadic() {
		return nil, false, unsup("%s.%s: expected one parameter and one result, the signature has %d/%d (pin drift — fail closed)", fn.Pkg().Path(), fn.Name(), sig.Params().Len(), sig.Results().Len())
	}
	pb, pok := sig.Params().At(0).Type().Underlying().(*types.Basic)
	rb, rok := sig.Results().At(0).Type().Underlying().(*types.Basic)
	if !pok || !rok || pb.Kind() != types.Int || rb.Kind() != types.Int {
		return nil, false, unsup("%s.%s: signature %s is not the pinned func(int) int (pin drift — fail closed)", fn.Pkg().Path(), fn.Name(), sig)
	}
	if len(c.Args) != 1 {
		return nil, false, unsup("%s.%s called with %d argument(s) (a multi-valued call as the sole argument is outside the lowering) — fail closed", fn.Pkg().Path(), fn.Name(), len(c.Args))
	}
	if inner, isCall := c.Args[0].(*ast.CallExpr); isCall {
		if _, isTup := e.goTypeOf(inner).(*types.Tuple); isTup {
			return nil, false, unsup("%s.%s with a tuple-splat argument list — fail closed", fn.Pkg().Path(), fn.Name())
		}
	}
	arg, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, false, err
	}
	resultTypes, err := e.emitResultTypes(sig)
	if err != nil {
		return nil, false, err
	}
	return map[string]any{"expr": "rand-intn", "callee": tag, "n": arg, "resultTypes": resultTypes}, true, nil
}

// refuseRandIntnDeferGo refuses `defer rand.Intn(n)` / `go rand.Intn(n)` BY NAME:
// the draw is defined at direct-call sites only; as a deferred/spawned FUNCTION
// VALUE the callee has no lowering (the `sync-op` / intercept precedent).
func (e *emitter) refuseRandIntnDeferGo(keyword string, c *ast.CallExpr) error {
	sel, ok := c.Fun.(*ast.SelectorExpr)
	if !ok {
		return nil
	}
	if fn, _, isRI := isRandIntnFunc(e.info.Uses[sel.Sel]); isRI {
		return unsup("%s %s.%s: the [0, n) draw lowers at direct-call sites only (the rand-intn primitive, window unit 5b); as a deferred/spawned FUNCTION VALUE it has no lowering — refused by name", keyword, fn.Pkg().Path(), fn.Name())
	}
	return nil
}
