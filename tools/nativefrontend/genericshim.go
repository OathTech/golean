// Generic-stdlib desugars — W4.3 item 1 landing B (docs/raft-w43-log.md):
// slices.SortFunc and cmp.Compare, the MajorityConfig.Describe pair
// (H-5, the W1.2 inheritance).
//
// Neither fits the E5 direct-call path because the callee is GENERIC:
//
//   - slices.SortFunc[S ~[]E, E any] emits as a call to the INJECTED
//     generic insertion-sort shim (stdlibshim.go), stenciled at the
//     call's element type through the ORDINARY mono pipeline
//     (registerFuncInst) — the same machinery user generics use, so
//     the shim's loops/swaps lower once per element type with full
//     collision checking. The S ~[]E freedom is NARROWED to S == []E
//     exactly (no subject or corpus site passes a named slice type;
//     fail closed with a message naming the bound).
//   - cmp.Compare[T Ordered] dispatches AT EMIT TIME on T's kind to a
//     monomorphic kind shim (unsigned/signed/string) with explicit
//     conversions — for integer and string kinds the shim IS
//     cmp.Compare's semantics; FLOAT kinds are excluded (the NaN arm
//     is float-specific latitude nothing needs) and refuse.
//
// Tie order under SortFunc is recorded LATITUDE: upstream documents
// "not guaranteed to be stable", so every cmp-consistent order
// conforms; our member (insertion sort) is stable and deterministic.
// Pinned tie-insensitively by slices/sortfunc-cmp/sort-ties-projected.

package main

import (
	"go/ast"
	"go/types"
)

// emitSortFuncCall: handled=true exactly for `slices.SortFunc(x, cmp)`.
func (e *emitter) emitSortFuncCall(c *ast.CallExpr, sel *ast.SelectorExpr) (any, bool, error) {
	x, ok := sel.X.(*ast.Ident)
	if !ok {
		return nil, false, nil
	}
	pkgName, ok := e.info.Uses[x].(*types.PkgName)
	if !ok || pkgName.Imported().Path() != "slices" || sel.Sel.Name != "SortFunc" {
		return nil, false, nil
	}
	if c.Ellipsis.IsValid() || len(c.Args) != 2 {
		return nil, false, unsup("slices.SortFunc call shape outside the modeled subset")
	}
	inst, ok := e.info.Instances[sel.Sel]
	if !ok || inst.TypeArgs.Len() != 2 {
		return nil, false, unsup("slices.SortFunc has no 2-argument instantiation record")
	}
	sliceT := inst.TypeArgs.At(0)
	elemT := inst.TypeArgs.At(1)
	if !types.Identical(sliceT, types.NewSlice(elemT)) {
		return nil, false, unsup("slices.SortFunc over the named slice type %s is outside the modeled subset (modeled: a plain []E first argument)", sliceT)
	}
	shimObj := e.pkg.Scope().Lookup(slicesSortFuncShimName)
	shimFn, okFn := shimObj.(*types.Func)
	if !okFn {
		return nil, false, unsup("slices.SortFunc shim %s not injected", slicesSortFuncShimName)
	}
	targs := []types.Type{elemT}
	mangled, err := e.instFuncId(e.funcWireName(shimFn), targs)
	if err != nil {
		return nil, false, err
	}
	if err := e.registerFuncInst(mangled, shimFn, targs); err != nil {
		return nil, false, err
	}
	gsig := shimFn.Type().(*types.Signature)
	csigT, err := types.Instantiate(e.instCtxt(), gsig, targs, false)
	if err != nil {
		return nil, false, unsup("instantiate %s at %s: %v", slicesSortFuncShimName, elemT, err)
	}
	args, err := e.emitCallArgs(csigT.(*types.Signature), c)
	if err != nil {
		return nil, false, err
	}
	return map[string]any{"expr": "call", "func": mangled,
		"args": args, "resultTypes": []any{}}, true, nil
}

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
		// Floats excluded on purpose: cmp.Compare's NaN arm is
		// float-specific ordering latitude nothing in scope needs.
		return nil, false, unsup("cmp.Compare over %s is outside the modeled subset (modeled: integer and string kinds; the float NaN arm is excluded)", t)
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
