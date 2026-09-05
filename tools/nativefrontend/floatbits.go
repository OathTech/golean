package main

// The `float-bits` PRIMITIVE (stdlib slice 3, 2026-09-04): `math.Float64bits`,
// `Float64frombits`, `Float32bits`, `Float32frombits` — the four documented
// bit-reinterpretation functions (deps/go/src/math/unsafe.go:21-41 @
// go1.26.5 — a file:line citation, like the runtime-source rows: `math` is
// not source-through, so the pinned-manifest `godoc:` grammar (G3) does
// not cover it) — lower to ONE machine expression op
// with a direction/width tag (`FloatBitsOp`, GoLean/GoCore/Syntax.lean;
// `floatBitsApply`, Ops.lean). ADMITTED [USER] 2026-09-04 (relayed by the
// [AGENT] coordinator, cited as relayed: «so the question is whether to add
// this as a primitive language operation? This sounds reasonable, do it»),
// counted as 1 of the register's 2 library-origin primitives
// (stdlibregister.go). Why a primitive and not source-through: the
// language has no operation for "the bits of a float" — math's own bodies
// are `*(*uint64)(unsafe.Pointer(&f))`, an `unsafe` site the H-3 quarantine
// refuses by doctrine — while the machine's float representation IS the bit
// pattern, so the op is the identity on the representation (NaN payloads,
// signed zero, quiet/signalling: bit-exact both ways; the one fail-closed
// arm, the machine's canonical NaN under `*bits`, is documented at
// `floatBitsApply` — inventory R7).
//
// The lowering is a PURE strict op (never hoisted — `emitCallNode` returns
// `false` for the effect flag, like a conversion); the pinned signatures are
// re-checked at every call, so a toolchain whose `math` differs from the pin
// refuses rather than lowering a different function.

import (
	"go/ast"
	"go/types"
)

const mathPkgPath = "math"

// floatBitsOps: the wire tag per math member, plus the pinned (param, result)
// basic kinds — `*bits` takes the float and yields the unsigned integer of the
// same width; `*frombits` the converse.
var floatBitsOps = map[string]struct {
	op     string
	param  types.BasicKind
	result types.BasicKind
}{
	"Float64bits":     {"f64bits", types.Float64, types.Uint64},
	"Float64frombits": {"f64frombits", types.Uint64, types.Float64},
	"Float32bits":     {"f32bits", types.Float32, types.Uint32},
	"Float32frombits": {"f32frombits", types.Uint32, types.Float32},
}

// isFloatBitsFunc reports whether obj is one of the four `math` package-level
// bit-reinterpretation functions (methods never route here).
func isFloatBitsFunc(obj types.Object) (*types.Func, bool) {
	fn, ok := obj.(*types.Func)
	if !ok || fn.Pkg() == nil || fn.Pkg().Path() != mathPkgPath {
		return nil, false
	}
	if _, listed := floatBitsOps[fn.Name()]; !listed {
		return nil, false
	}
	sig, ok := fn.Type().(*types.Signature)
	if !ok || sig.Recv() != nil {
		return nil, false
	}
	return fn, true
}

// emitFloatBitsCall lowers a direct call of one of the four functions to the
// `float-bits` expression node. The signature is checked against the pin
// (one parameter and one result of the recorded basic kinds); any drift
// refuses by name.
func (e *emitter) emitFloatBitsCall(c *ast.CallExpr, fn *types.Func) (any, bool, error) {
	spec := floatBitsOps[fn.Name()]
	sig, _ := fn.Type().(*types.Signature)
	if sig == nil || sig.Params().Len() != 1 || sig.Results().Len() != 1 {
		return nil, false, unsup("math.%s: expected one parameter and one result, the signature has %d/%d (pin drift — fail closed)", fn.Name(), sig.Params().Len(), sig.Results().Len())
	}
	pb, pok := sig.Params().At(0).Type().Underlying().(*types.Basic)
	rb, rok := sig.Results().At(0).Type().Underlying().(*types.Basic)
	if !pok || !rok || pb.Kind() != spec.param || rb.Kind() != spec.result {
		return nil, false, unsup("math.%s: signature %s is not the pinned %s -> %s (pin drift — fail closed)", fn.Name(), sig, types.Typ[spec.param], types.Typ[spec.result])
	}
	if len(c.Args) != 1 {
		return nil, false, unsup("math.%s called with %d argument(s) (a multi-valued call as the sole argument is outside the lowering) — fail closed", fn.Name(), len(c.Args))
	}
	if inner, isCall := c.Args[0].(*ast.CallExpr); isCall {
		if _, isTup := e.goTypeOf(inner).(*types.Tuple); isTup {
			return nil, false, unsup("math.%s with a tuple-splat argument list — fail closed", fn.Name())
		}
	}
	arg, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, false, err
	}
	return map[string]any{"expr": "float-bits", "op": spec.op, "x": arg}, false, nil
}
