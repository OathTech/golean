// cmp.Compare kind-dispatch desugar — the ONE generic desugar RETAINED
// after stdlib source-through slice 2 (2026-09-03), by the slice's STOP
// rule: retiring it flipped a GREEN row red. `cmp` IS a source-through
// library unit and the real generic `cmp.Compare[T]` lowers for every
// package-level type argument (floats and the NaN arm included —
// stdlib-source/cmp-compare/*); but a call at a FUNCTION-LOCAL defined
// type (`type index uint64` inside a body, the quorum.Index shape the
// row slices/sortfunc-cmp/cmp-compare-kinds pins) instantiates the
// real generic at a type mono.go REFUSES to name (audit response M3:
// gc renders function-local types in instantiation renderings with a
// compiler-internal unique suffix — "refused rather than guessed"). The
// kind dispatch below never instantiates anything (it converts to the
// kind's shim), so it sidesteps the naming rule, which is why the row
// was green under it. This is a FRONTEND GENERALITY gap in generic
// instantiation at local types (the same gap already reds
// slices/sortfunc-cmp/sortfunc-local-type), not a cmp.Compare gap; its
// retirement is posed to the [USER] in the slice-2 evidence README
// (either accept the designed red like BUG-089, or land the
// local-type instantiation naming first). D-002: the body is unchanged.
//
// Originally W4.3 item 1 landing B (docs/raft-w43-log.md): cmp.Compare[T
// Ordered] dispatches AT EMIT TIME on T's kind to a monomorphic kind shim
// (unsigned/signed/string) with explicit conversions — for integer and
// string kinds the shim IS cmp.Compare's semantics; FLOAT kinds refuse
// here (a float call site can use the real generic: the refusal names
// it).

package main

import (
	"go/ast"
	"go/types"
)

// emitCmpCompareCall: handled=true exactly for `cmp.Compare(a, b)`.
func (e *emitter) emitCmpCompareCall(c *ast.CallExpr, sel *ast.SelectorExpr) (any, bool, error) {
	x, ok := sel.X.(*ast.Ident)
	if !ok {
		return nil, false, nil
	}
	pkgName, ok := e.info.Uses[x].(*types.PkgName)
	if !ok || pkgName.Imported().Path() != "cmp" || sel.Sel.Name != "Compare" {
		return nil, false, nil
	}
	if c.Ellipsis.IsValid() || len(c.Args) != 2 {
		return nil, false, unsup("cmp.Compare call shape outside the modeled subset")
	}
	inst, ok := e.info.Instances[sel.Sel]
	if !ok || inst.TypeArgs.Len() != 1 {
		return nil, false, unsup("cmp.Compare has no instantiation record")
	}
	t := inst.TypeArgs.At(0)
	basic, _ := t.Underlying().(*types.Basic)
	if basic == nil {
		return nil, false, unsup("cmp.Compare over non-basic type %s is outside the modeled subset", t)
	}
	var shimName string
	var target types.Type
	switch {
	case basic.Info()&types.IsInteger != 0 && basic.Info()&types.IsUnsigned != 0:
		shimName, target = cmpCompareUintShimName, types.Typ[types.Uint64]
	case basic.Info()&types.IsInteger != 0:
		shimName, target = cmpCompareIntShimName, types.Typ[types.Int64]
	case basic.Info()&types.IsString != 0:
		shimName, target = cmpCompareStringShimName, types.Typ[types.String]
	default:
		// Floats: not handled here — the call falls through to the
		// REAL generic cmp.Compare[T] (source-through `cmp`, NaN arm
		// included; stdlib-source/cmp-compare/* pins it).
		return nil, false, nil
	}
	shimObj := e.pkg.Scope().Lookup(shimName)
	shimFn, okFn := shimObj.(*types.Func)
	if !okFn {
		return nil, false, unsup("cmp.Compare shim %s not injected", shimName)
	}
	tw, err := e.emitType(target)
	if err != nil {
		return nil, false, err
	}
	args := []any{}
	for _, a := range c.Args {
		node, err := e.emitExpr(a)
		if err != nil {
			return nil, false, err
		}
		if !types.Identical(e.goTypeOf(a), target) {
			node = map[string]any{"expr": "convert", "target": tw, "x": node}
		}
		args = append(args, node)
	}
	return map[string]any{"expr": "call", "func": e.funcWireName(shimFn),
		"args": args, "resultTypes": []any{intType("int")}}, true, nil
}
