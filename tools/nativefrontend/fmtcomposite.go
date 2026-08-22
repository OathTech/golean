// %v / %+v COMPOSITE rendering — W4.3 item 1 (docs/raft-w43-log.md),
// the rendered-tier surface. Extends the H-6 fmt desugar
// (fmtdesugar.go) with an emit-time RECURSIVE matrix over the
// argument's STATIC type:
//
//   composite := slice-of leaf | named-struct-of leaf
//   leaf      := integer kinds | string kinds | bool
//              | error/Stringer implementor (consulted per
//                element/field, as gc's printValue does at depth —
//                probed artifacts/w43/probe-fmt D1-D4 — but NEVER
//                below an unexported field: crossing one taints the
//                subtree and it renders RAW, as gc's reflection does;
//                audit R1-F1, gc-probed .tmp/fixround-probes/f1)
//              | composite (recursively; cycle-guarded, fail closed)
//
// Everything outside — maps, pointers, interfaces at depth, anonymous
// structs, floats — REFUSES per-declaration naming the leaf (the
// fmt/v-composites boundary rows pin the refusals). gc-probed forms
// (artifacts/w43/probe-fmt A/B/C/D): slices are `[a b c]`
// space-separated with nil and empty both `[]`; structs are `{a b}`
// (`%v`) / `{name:a name:b}` (`%+v`, the flag propagating to every
// depth); []byte renders as a decimal byte list; a Stringer
// element/field renders its String() result under fmt's
// recover-and-render (the element render is `%!v(PANIC=...)` on a
// panicking method).
//
// MECHANISM. The desugar generates a LIFTED renderer function per
// composite call site (`<fn>$fmtc<N>` for the top value,
// `<fn>$fmtsl<N>` per slice level): plain wire statements (a counted
// for-loop over the slice, per-field concatenation for structs), every
// helper call bound to a temp (calls are statements on the wire), leaf
// rendering through the SAME goleanShimFmt* helpers as the scalar
// matrix — so composite cells inherit the scalar cells' probed
// behavior. No GoCore change, no new wire node, no runtime reflection:
// the type recursion happens entirely at emit time.

package main

import (
	"go/ast"
	"go/types"
)

// fmtCompositeArg is the hook fmtVerbArg calls after the scalar matrix
// misses on %v/%+v: handled=true iff the STATIC type enters the
// composite matrix (a slice, or a named struct). A modeled top with an
// unmodeled leaf REFUSES (error), naming the leaf.
func (e *emitter) fmtCompositeArg(fn string, v fmtVerb, arg ast.Expr, k int) (*fmtArgPlan, bool, error) {
	argTy := e.goTypeOf(arg)
	switch argTy.Underlying().(type) {
	case *types.Slice:
	case *types.Struct:
		if _, ok := e.namedTypeName(argTy); !ok {
			return nil, false, nil // anonymous struct: the standard refusal
		}
	default:
		return nil, false, nil
	}
	liftName, err := e.fmtCompositeTopLift(fn, v.plus, argTy)
	if err != nil {
		return nil, true, err
	}
	tw, err := e.emitType(argTy)
	if err != nil {
		return nil, true, err
	}
	node, err := e.emitExpr(arg)
	if err != nil {
		return nil, true, err
	}
	strTy := map[string]any{"kind": "string"}
	pname := "$a" + itoa(k)
	paramRef := map[string]any{"expr": "ident", "name": pname, "type": tw}
	return &fmtArgPlan{
		callArgs: []any{node},
		params:   []any{map[string]any{"id": pname, "type": tw}},
		body: map[string]any{"expr": "call", "func": liftName,
			"args": []any{paramRef}, "resultTypes": []any{strTy}},
	}, true, nil
}

// fmtCompositeTopLift generates the top-level renderer lift
// `func(<T>) string` and returns its name.
func (e *emitter) fmtCompositeTopLift(fn string, plus bool, t types.Type) (string, error) {
	strTy := map[string]any{"kind": "string"}
	tw, err := e.emitType(t)
	if err != nil {
		return "", err
	}
	name := e.curFuncName + "$fmtc" + itoa(e.liftSeq)
	e.liftSeq++
	val := map[string]any{"expr": "ident", "name": "$x", "type": tw}
	tmp := 0
	stmts, piece, err := e.fmtRenderValue(fn, plus, t, val, map[string]bool{}, &tmp, false)
	if err != nil {
		return "", err
	}
	stmts = append(stmts, map[string]any{"stmt": "return", "results": []any{piece}})
	e.lifted = append(e.lifted, map[string]any{
		"name":     name,
		"params":   []any{map[string]any{"id": "$x", "type": tw}},
		"results":  []any{map[string]any{"id": "$res0", "type": strTy}},
		"variadic": false,
		"body":     map[string]any{"stmt": "block", "body": stmts},
	})
	return name, nil
}

// fmtRenderValue returns (stmts, piece) rendering `val` of type t under
// %v/%+v: stmts bind every call to a temp (in evaluation order — left
// to right, matching gc's per-operand walk), piece is a PURE expression
// over those temps.
//
// `tainted` (audit R1-F1/R4-C-2): true once the render path has
// CROSSED AN UNEXPORTED FIELD. gc renders through reflection, and a
// value reached via an unexported field cannot be interfaced
// (reflect's CanInterface is false), so fmt SKIPS method consultation
// for that value AND everything below it — the subtree renders raw
// (gc-probed .tmp/fixround-probes/f1: `{E<1> 2}`, `{in:{X:3} A:E<4>}`,
// `{bs:[5 6]}`). A tainted leaf therefore bypasses the error/Stringer
// arm and renders through the kind matrix; a tainted leaf OUTSIDE the
// raw matrix refuses exactly like any other unmodeled leaf (fail
// closed — the refusal names the leaf type).
func (e *emitter) fmtRenderValue(fn string, plus bool, t types.Type, val any,
	visiting map[string]bool, tmp *int, tainted bool) ([]any, any, error) {
	strTy := map[string]any{"kind": "string"}
	verbName := "%v"
	if plus {
		verbName = "%+v"
	}
	bindCall := func(call map[string]any) (stmts []any, piece any) {
		tname := "$c" + itoa(*tmp)
		*tmp++
		return []any{map[string]any{"stmt": "assign", "define": true,
				"lhs": []any{map[string]any{"target": "declare", "id": tname, "type": strTy}},
				"rhs": []any{call}}},
			map[string]any{"expr": "ident", "name": tname, "type": strTy}
	}
	shimCall := func(shim string, args ...any) map[string]any {
		return map[string]any{"expr": "call", "func": e.fmtShimWireName(shim),
			"args": args, "resultTypes": []any{strTy}}
	}

	// error/Stringer precedence per element/field, exactly as at top
	// level (gc consults handleMethods at every depth). Concrete
	// non-pointer implementors only: a pointer element/field is outside
	// the composite subset (below), and an interface-typed leaf other
	// than `error` refuses like the scalar matrix does.
	errIface := types.Universe.Lookup("error").Type().Underlying().(*types.Interface)
	if !tainted && !types.IsInterface(t) {
		if _, isPtr := types.Unalias(t).(*types.Pointer); !isPtr {
			// fmt.Formatter precedence at depth, exactly as at top
			// level (audit R1-F2; gc-probed {FMT:v:1} at depth). A
			// TAINTED leaf is exempt with the rest of the method arm:
			// gc cannot interface it, so Format is not consulted below
			// an unexported field (probed {2}).
			if err := e.refuseFormatter(fn, verbName, t); err != nil {
				return nil, nil, err
			}
			methodName := ""
			if types.Implements(t, errIface) {
				methodName = "Error"
			} else if types.Implements(t, fmtStringerIface) {
				methodName = "String"
			}
			if methodName != "" {
				obj, index, _ := types.LookupFieldOrMethod(t, true, e.pkg, methodName)
				mfn, okFn := obj.(*types.Func)
				if !okFn || len(index) != 1 {
					return nil, nil, unsup("fmt.%s verb %s: composite leaf %s's %s method is promoted or missing (outside the modeled subset)", fn, verbName, t, methodName)
				}
				recvT := mfn.Type().(*types.Signature).Recv().Type()
				if _, pointerRecv := recvT.(*types.Pointer); pointerRecv {
					return nil, nil, unsup("fmt.%s verb %s: composite leaf %s implements %s via a pointer receiver (outside the modeled composite subset)", fn, verbName, t, methodName)
				}
				typeName, okName := e.namedTypeName(t)
				if !okName {
					return nil, nil, unsup("fmt.%s verb %s: composite leaf method on unnameable type %s", fn, verbName, t)
				}
				mv := map[string]any{"expr": "func-value",
					"func": typeName + "." + methodName, "captured": []any{val}}
				stmts, piece := bindCall(shimCall("goleanShimFmtRender",
					stringLitNode("v"), stringLitNode(methodName),
					map[string]any{"expr": "bool", "value": false}, mv))
				return stmts, piece, nil
			}
		}
	}

	if basic, ok := t.Underlying().(*types.Basic); ok {
		convert := func(target types.Type) (any, error) {
			tw, err := e.emitType(target)
			if err != nil {
				return nil, err
			}
			if types.Identical(t, target) {
				return val, nil
			}
			return map[string]any{"expr": "convert", "target": tw, "x": val}, nil
		}
		switch {
		case basic.Info()&types.IsString != 0:
			node, err := convert(types.Typ[types.String])
			return nil, node, err
		case basic.Info()&types.IsInteger != 0 && basic.Info()&types.IsUnsigned != 0:
			node, err := convert(types.Typ[types.Uint64])
			if err != nil {
				return nil, nil, err
			}
			stmts, piece := bindCall(shimCall("goleanShimFmtUint", node))
			return stmts, piece, nil
		case basic.Info()&types.IsInteger != 0:
			node, err := convert(types.Typ[types.Int64])
			if err != nil {
				return nil, nil, err
			}
			stmts, piece := bindCall(shimCall("goleanShimFmtInt", node))
			return stmts, piece, nil
		case basic.Info()&types.IsBoolean != 0:
			node, err := convert(types.Typ[types.Bool])
			if err != nil {
				return nil, nil, err
			}
			stmts, piece := bindCall(shimCall("goleanShimFmtBool", node))
			return stmts, piece, nil
		}
		return nil, nil, unsup("fmt.%s verb %s: composite leaf of type %s is outside the modeled composite subset (fail closed — widen with a differential pin first)", fn, verbName, t)
	}

	key := types.TypeString(t, nil)
	if visiting[key] {
		return nil, nil, unsup("fmt.%s verb %s: recursive composite type %s (cycle — outside the modeled composite subset)", fn, verbName, t)
	}

	if sl, ok := t.Underlying().(*types.Slice); ok {
		visiting[key] = true
		liftName, err := e.fmtSliceLift(fn, plus, t, sl.Elem(), visiting, tainted)
		delete(visiting, key)
		if err != nil {
			return nil, nil, err
		}
		strCall := map[string]any{"expr": "call", "func": liftName,
			"args": []any{val}, "resultTypes": []any{strTy}}
		stmts, piece := bindCall(strCall)
		return stmts, piece, nil
	}

	if st, ok := t.Underlying().(*types.Struct); ok {
		typeName, okName := e.namedTypeName(t)
		if !okName {
			return nil, nil, unsup("fmt.%s verb %s: anonymous struct composite %s is outside the modeled composite subset", fn, verbName, t)
		}
		visiting[key] = true
		defer delete(visiting, key)
		concat := func(a, b any) any {
			return map[string]any{"expr": "binary", "op": "+",
				"x": a, "y": b, "operandType": strTy}
		}
		var stmts []any
		piece := any(stringLitNode("{"))
		for i := 0; i < st.NumFields(); i++ {
			f := st.Field(i)
			lead := ""
			if i > 0 {
				lead = " "
			}
			if plus {
				lead += f.Name() + ":"
			}
			if lead != "" {
				piece = concat(piece, stringLitNode(lead))
			}
			fieldNode := map[string]any{"expr": "field-get", "recv": val,
				"typeId": typeName, "field": f.Name()}
			// Crossing an unexported field taints the subtree (R1-F1).
			fstmts, fpiece, err := e.fmtRenderValue(fn, plus, f.Type(), fieldNode, visiting, tmp,
				tainted || !f.Exported())
			if err != nil {
				return nil, nil, err
			}
			stmts = append(stmts, fstmts...)
			piece = concat(piece, fpiece)
		}
		piece = concat(piece, stringLitNode("}"))
		return stmts, piece, nil
	}

	return nil, nil, unsup("fmt.%s verb %s: composite leaf of type %s is outside the modeled composite subset (fail closed — widen with a differential pin first)", fn, verbName, t)
}

// fmtSliceLift generates `func(<sliceT>) string` rendering `[a b c]`
// with a counted loop, and returns its name. Nil and empty both render
// `[]` (the loop body never runs) — gc-probed. `tainted` carries the
// unexported-crossing flag into the element render (R1-F1).
func (e *emitter) fmtSliceLift(fn string, plus bool, sliceT types.Type, elemT types.Type,
	visiting map[string]bool, tainted bool) (string, error) {
	strTy := map[string]any{"kind": "string"}
	intTy := map[string]any{"kind": "int", "int": "int"}
	sliceW, err := e.emitType(sliceT)
	if err != nil {
		return "", err
	}
	elemW, err := e.emitType(elemT)
	if err != nil {
		return "", err
	}
	name := e.curFuncName + "$fmtsl" + itoa(e.liftSeq)
	e.liftSeq++

	sRef := map[string]any{"expr": "ident", "name": "$s", "type": sliceW}
	iRef := map[string]any{"expr": "ident", "name": "$i", "type": intTy}
	outRef := map[string]any{"expr": "ident", "name": "$out", "type": strTy}
	eRef := map[string]any{"expr": "ident", "name": "$e", "type": elemW}
	intLit := func(v int) map[string]any {
		return map[string]any{"expr": "int", "value": itoa(v), "type": intTy}
	}
	concat := func(a, b any) any {
		return map[string]any{"expr": "binary", "op": "+",
			"x": a, "y": b, "operandType": strTy}
	}
	assignOut := func(rhs any) map[string]any {
		return map[string]any{"stmt": "assign",
			"lhs": []any{map[string]any{"target": "var", "id": "$out"}},
			"rhs": []any{rhs}}
	}

	tmp := 0
	elemStmts, elemPiece, err := e.fmtRenderValue(fn, plus, elemT, eRef, visiting, &tmp, tainted)
	if err != nil {
		return "", err
	}

	loopBody := []any{
		map[string]any{"stmt": "if",
			"cond": map[string]any{"expr": "binary", "op": ">", "x": iRef, "y": intLit(0)},
			"then": map[string]any{"stmt": "block",
				"body": []any{assignOut(concat(outRef, stringLitNode(" ")))}}},
		map[string]any{"stmt": "assign", "define": true,
			"lhs": []any{map[string]any{"target": "declare", "id": "$e", "type": elemW}},
			"rhs": []any{map[string]any{"expr": "index-get", "base": sRef, "index": iRef}}},
	}
	loopBody = append(loopBody, elemStmts...)
	loopBody = append(loopBody, assignOut(concat(outRef, elemPiece)))

	body := []any{
		map[string]any{"stmt": "assign", "define": true,
			"lhs": []any{map[string]any{"target": "declare", "id": "$out", "type": strTy}},
			"rhs": []any{stringLitNode("[")}},
		map[string]any{"stmt": "for",
			"init": map[string]any{"stmt": "assign", "define": true,
				"lhs": []any{map[string]any{"target": "declare", "id": "$i", "type": intTy}},
				"rhs": []any{intLit(0)}},
			"cond": map[string]any{"expr": "binary", "op": "<", "x": iRef,
				"y": map[string]any{"expr": "builtin-len", "operand": sRef, "operandType": sliceW}},
			"post": map[string]any{"stmt": "assign",
				"lhs": []any{map[string]any{"target": "var", "id": "$i"}},
				"rhs": []any{map[string]any{"expr": "binary", "op": "+",
					"x": iRef, "y": intLit(1), "operandType": intTy}}},
			"body": map[string]any{"stmt": "block", "body": loopBody}},
		map[string]any{"stmt": "return",
			"results": []any{concat(outRef, stringLitNode("]"))}},
	}
	e.lifted = append(e.lifted, map[string]any{
		"name":     name,
		"params":   []any{map[string]any{"id": "$s", "type": sliceW}},
		"results":  []any{map[string]any{"id": "$res0", "type": strTy}},
		"variadic": false,
		"body":     map[string]any{"stmt": "block", "body": body},
	})
	return name, nil
}
