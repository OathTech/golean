// %v / %+v COMPOSITE rendering — W4.3 item 1 (docs/raft-w43-log.md),
// the rendered-tier surface. Extends the H-6 fmt desugar
// (fmtdesugar.go) with an emit-time RECURSIVE matrix over the
// argument's STATIC type:
//
//   composite := slice-of leaf | named-struct-of leaf
//   leaf      := integer kinds | string kinds | bool
//              | error/Stringer implementor (consulted per
//                element/field, as gc's printValue does at depth —
//                probed artifacts/w43/probe-fmt D1-D4 — but NOT
//                below an unexported field, mirroring reflect's two
//                read-only flags: a NON-EMBEDDED unexported field
//                taints its whole subtree RAW (audit R1-F1, probed
//                .tmp/fixround-probes/f1), an EMBEDDED one suppresses
//                methods at its own level only (delta-review
//                CRITICAL-1, probed .tmp/deltarev) — see
//                fmtRenderValue's doc comment for the exact rule)
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
	stmts, piece, err := e.fmtRenderValue(fn, plus, t, val, map[string]bool{}, &tmp, false, false)
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
// `sticky`/`embedRO` (audit R1-F1/R4-C-2; SPLIT by the delta-review's
// CRITICAL-1) model reflect's TWO read-only flags, which the first cut
// conflated into one `tainted` bool. gc renders through reflection and
// a value whose flagRO is set cannot be interfaced (CanInterface is
// false), so fmt SKIPS method consultation for it — but WHICH bit is
// set decides whether the suppression is inherited:
//
//	// reflect/value.go, Value.Field:
//	fl := v.flag&(flagStickyRO|flagIndir|flagAddr) | flag(typ.Kind())
//	if !field.name.IsExported() {
//	    if field.embedded() { fl |= flagEmbedRO } else { fl |= flagStickyRO }
//	}
//
//   - `sticky` = flagStickyRO — set by crossing a NON-EMBEDDED
//     unexported field, and INHERITED by the whole subtree below it
//     (Field propagates exactly this bit).
//   - `embedRO` = flagEmbedRO — set by crossing an EMBEDDED unexported
//     field. CanInterface is false AT THAT LEVEL (so no method arm
//     there), but Field does NOT propagate it: the embedded struct's
//     own exported fields start clean and their methods ARE consulted.
//
// Every OTHER descent (Index/Elem/MapIndex) goes through `flag.ro()`,
// which collapses EITHER bit to sticky — so the slice lift below is
// handed `sticky || embedRO`, never embedRO on its own.
//
// gc-probed, .tmp/fixround-probes/f1 (the sticky leg: `{E<1> 2}`,
// `{in:{X:3} A:E<4>}`, `{bs:[5 6]}`) and .tmp/deltarev/{v1,v6,w3,x1,
// p1..p7} (the embed leg: `{{E<4>}}`, `{{{E<4>}}}`, `{{{4}}}`, `{{4}}`,
// `{[5 6]}`, `{{[E<5> E<6>]}}`, `{{E<4>} {E<5>}}`, `{{E<1> {E<2>}}}`),
// pinned as Corpus/coverage/exec/fmt/v-composites' `emb-*` rows.
//
// A read-only leaf therefore bypasses the Formatter/error/Stringer arm
// and renders through the kind matrix; one OUTSIDE the raw matrix
// refuses exactly like any other unmodeled leaf (fail closed — the
// refusal names the leaf type).
func (e *emitter) fmtRenderValue(fn string, plus bool, t types.Type, val any,
	visiting map[string]bool, tmp *int, sticky bool, embedRO bool) ([]any, any, error) {
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
	if !sticky && !embedRO && !types.IsInterface(t) {
		if _, isPtr := types.Unalias(t).(*types.Pointer); !isPtr {
			// fmt.Formatter precedence at depth, exactly as at top
			// level (audit R1-F2; gc-probed {FMT:v:1} at depth). A
			// read-only leaf is exempt with the rest of the method arm:
			// gc cannot interface it, so Format is not consulted below
			// a non-embedded unexported field (probed {2}). Below an
			// EMBEDDED one it IS consulted one level down, which is why
			// embedRO must not reach here from the recursion (probed
			// {{FMT:v:1}}, .tmp/deltarev/x1 — row emb-formatter-below).
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
		// reflect's flag.ro(): Index() collapses EITHER read-only bit to
		// sticky, so an embedded-unexported slice DOES taint its
		// elements (probed `{[5 6]}`, .tmp/deltarev/p1).
		liftName, err := e.fmtSliceLift(fn, plus, t, sl.Elem(), visiting, sticky || embedRO)
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
			// Value.Field verbatim (R1-F1 + delta-review CRITICAL-1):
			// the child inherits ONLY the sticky bit; an unexported
			// field adds sticky when non-embedded, embed-RO (level
			// only) when embedded.
			unexpEmbed := !f.Exported() && f.Embedded()
			fstmts, fpiece, err := e.fmtRenderValue(fn, plus, f.Type(), fieldNode, visiting, tmp,
				sticky || (!f.Exported() && !f.Embedded()), unexpEmbed)
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
// `[]` (the loop body never runs) — gc-probed. `sticky` carries the
// read-only flag into the element render (R1-F1); it is ALREADY
// collapsed by the caller, because reflect's Index() maps either
// read-only bit to flagStickyRO (delta-review CRITICAL-1) — there is
// deliberately no embedRO parameter here.
func (e *emitter) fmtSliceLift(fn string, plus bool, sliceT types.Type, elemT types.Type,
	visiting map[string]bool, sticky bool) (string, error) {
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
	elemStmts, elemPiece, err := e.fmtRenderValue(fn, plus, elemT, eRef, visiting, &tmp, sticky, false)
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
