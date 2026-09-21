package main

// unseq_lower.go — Stage C C2: the source-to-graph LOWERING of an admitted sweep
// (design docs/2026-09-19_unseq-stage-c-design.md §6; the decision procedure is
// unseq.go's `unseqClassify`, consulted by emitStmtList BEFORE this runs — a sweep
// reaches emitUnseqSweep only when admitted, so every refusal below is an
// internal shape breach, named, never a silent fallback).
//
// THE GRAPH. One `unseq` node per sweep (design §4): typed VALUE cells `$u<n>`,
// TARGET binders `$t<n>` (n from the emitter's temp counter — unique per
// function beside the `$c<n>` hoist temps), occurrences in CANONICAL RANK order,
// the phase-2 stores, the completion `then`. Value dependencies are implied by
// slot mentions; ORDER prerequisites (`after`) carry E1 — every call, non-constant
// len/cap and logical operation follows the previous event anchor in lexical
// order, a logical operation anchoring at its ENTRY for earlier events and its
// COMPLETION for later ones (v2.1 §1 E1, review R2); `region` carries G.
//
// CANONICAL ORDER = today's ANF (v2.1 §3.5), at EVERY nesting level: a level's
// list is its EVENT BLOCKS (each a nested call / len / guard with its own operand
// subtree, itself in canonical order, the event last) followed by the level's
// RESIDUAL (its reads / ops / targets / loads, in lexical order) — legacy hoists
// every call out of an argument list before the residual call statement reads
// its sibling operands (`g(a[0], f())`: f, then a[0], then g). The all-zero tape
// then realizes calls first, reads late: gc's realization where gc is
// call-first; BUG-104's target plan and load move late — the intended flip.
// Producers precede consumers at every level (post-order emission; an event's
// operands live in its own frame), so the list is a linear extension of every
// edge (decoder D7).
//
// READS AND ATOMS. A constant or a PRIVATE local is an atom (order-transparent,
// v2.1 §1); an ADDRESS-TAKEN local is a READ occurrence (`eval` of the ident); a
// PACKAGE-LEVEL variable (Stage E E1, 2026-09-21 — unqualified `g` or a
// source-package qualified `pkg.V`) is a READ occurrence whose head is the
// frontend's own spelling of a global read, `deref(globaladdr gid)` (emitIdent /
// emitQualifiedSelector); as a TARGET its identity has no operands, so its store
// rides `then` (`assign addr(globaladdr) = $u`) and a compound form's load is
// that same READ occurrence — one identity, nothing to freeze; a
// slice element is base atom + index atom + ONE checked access (N1 SPLIT); a
// private compound target's read is folded into the op head and its store rides
// `then` (a plain-var plan has no operands and checks nothing; a `load` there
// would mint a spurious wide pick per loop iteration — design §7); a slice-element
// target is a `target` plan on FROZEN atoms (the header through a slot when the
// base is address-taken, through the local's own read at the plan step when
// private — never `&a`, Stage B F2) shared by the `load` and the store.
//
// THE MIXTURE GUARD. The lowering runs with `probeSuppress` raised and asserts the
// hoist accumulator unchanged afterwards: a legacy hoist or probe produced inside
// a graph lowering is refused by name (v2.1 §3.7: never a mixture).

import (
	"go/ast"
	"go/token"
	"go/types"
)

// unseqFrame is one level of the canonical partition: the EVENT blocks lowered
// at this level (each block = a nested event with its own operand subtree,
// already in canonical order) and the RESIDUAL occurrences (reads / ops /
// targets / loads) of this level. A level's canonical list is events ++
// residual (++ the event that owns the level, appended by its caller).
type unseqFrame struct {
	events   []any
	residual []any
}

type unseqBuilder struct {
	e      *emitter
	ctx    *unseqCtx
	cells  []any
	frames []*unseqFrame // frames[0] is the sweep level; a call / guard pushes a frame for its operand subtree
	stores []any
	anchor string // the E1 anchor: the last event / completion of the current lexical sequence
	region string // the enclosing guard ("" = top level)
	occSeq int
	addr   map[types.Object]bool
}

func (e *emitter) newUnseqBuilder(ctx *unseqCtx) *unseqBuilder {
	return &unseqBuilder{e: e, ctx: ctx, addr: e.unseqAddrTaken(ctx.body), frames: []*unseqFrame{{}}}
}

func (b *unseqBuilder) top() *unseqFrame { return b.frames[len(b.frames)-1] }

// push opens a frame for an event's operand subtree; pop closes it and returns
// its canonical list (nested event blocks first, then this level's residual).
func (b *unseqBuilder) push() { b.frames = append(b.frames, &unseqFrame{}) }
func (b *unseqBuilder) pop() []any {
	f := b.top()
	b.frames = b.frames[:len(b.frames)-1]
	return append(append([]any{}, f.events...), f.residual...)
}

// emitEventBlock appends a completed event block (the event's subtree in
// canonical order, then the event itself) at the current level.
func (b *unseqBuilder) emitEventBlock(block []any) {
	f := b.top()
	f.events = append(f.events, block...)
}

func (b *unseqBuilder) newCell(ty any) string {
	name := "$u" + itoa(b.e.tmpSeq)
	b.e.tmpSeq++
	b.cells = append(b.cells, map[string]any{"id": name, "type": ty})
	return name
}

func (b *unseqBuilder) newTargetBinder() string {
	name := "$t" + itoa(b.e.tmpSeq)
	b.e.tmpSeq++
	return name
}

func (b *unseqBuilder) occName(kind string) string {
	n := kind + itoa(b.occSeq)
	b.occSeq++
	return n
}

// emit places a NON-event occurrence (a read, op, target plan or load) in the
// current level's residual — after every event block of that level in the
// canonical list (legacy's "calls first, reads late": the residual expression
// evaluates after the hoisted temps, at every nesting level). `region` is
// attached here for every occurrence lowered inside a guard's region.
func (b *unseqBuilder) emit(o map[string]any) {
	if b.region != "" {
		o["region"] = b.region
	}
	f := b.top()
	f.residual = append(f.residual, o)
}

// eventAfter returns the `after` list for an event: the current anchor, if any.
func (b *unseqBuilder) eventAfter() []any {
	if b.anchor == "" {
		return nil
	}
	return []any{b.anchor}
}

func slotIdent(name string, ty any) map[string]any {
	return map[string]any{"expr": "ident", "name": name, "type": ty}
}

func isSlotIdent(w any) bool {
	m, ok := w.(map[string]any)
	if !ok || m["expr"] != "ident" {
		return false
	}
	n, _ := m["name"].(string)
	return len(n) > 0 && n[0] == '$'
}

// evalOcc emits an `eval` occurrence producing a fresh cell of type ty from head.
func (b *unseqBuilder) evalOcc(kind string, ty any, head map[string]any) any {
	cell := b.newCell(ty)
	head["type"] = ty
	b.emit(map[string]any{"name": b.occName(kind), "kind": "eval", "bind": cell, "head": head})
	return slotIdent(cell, ty)
}

// ensureCell returns a slot for w, copying a constant / private atom into a fresh
// cell when the consumer needs a CELL (a store value, a guard test).
func (b *unseqBuilder) ensureCell(w any, ty any) (string, any) {
	if isSlotIdent(w) {
		m := w.(map[string]any)
		return m["name"].(string), w
	}
	head := map[string]any{}
	for k, v := range w.(map[string]any) {
		head[k] = v
	}
	slot := b.evalOcc("copy", ty, head)
	return slot.(map[string]any)["name"].(string), slot
}

// value lowers an operand to an ATOM wire (a constant, a private local, or a slot),
// emitting the occurrences it needs. Mirrors unseqExpr's admission case by case.
func (b *unseqBuilder) value(x ast.Expr) (any, error) {
	e := b.e
	if tv, ok := e.typesEntry(x); ok && tv.Value != nil {
		return e.emitConstValue(tv)
	}
	switch v := x.(type) {
	case *ast.ParenExpr:
		return b.value(v.X)
	case *ast.Ident:
		obj := e.info.Uses[v]
		ty, err := e.typeOf(v)
		if err != nil {
			return nil, err
		}
		w, err := e.emitIdent(v)
		if err != nil {
			return nil, err
		}
		m, ok := w.(map[string]any)
		if _, isPkg := e.isPackageVar(obj); isPkg {
			// Stage E E1: a package-level variable's read — `deref(globaladdr)`,
			// the head of a READ occurrence (an unseeded / poisoned cell has
			// already refused by name inside emitIdent, as on the legacy path).
			if !ok || m["expr"] != "deref" {
				return nil, unsup("unseq lowering: package-level variable %s did not lower to a global read (%v) — outside the admitted grammar", v.Name, w)
			}
			m["type"] = ty
			return b.evalOcc("read", ty, m), nil
		}
		if !ok || m["expr"] != "ident" {
			return nil, unsup("unseq lowering: local %s did not lower to an identifier (%v) — outside the admitted grammar", v.Name, w)
		}
		m["type"] = ty
		if b.addr[obj] {
			return b.evalOcc("read", ty, m), nil // a READ occurrence of a mutable location
		}
		return m, nil // a private local: an admitted stable read, order-transparent
	case *ast.IndexExpr:
		base, err := b.value(v.X)
		if err != nil {
			return nil, err
		}
		idx, err := b.value(v.Index)
		if err != nil {
			return nil, err
		}
		ty, err := e.typeOf(v)
		if err != nil {
			return nil, err
		}
		return b.evalOcc("access", ty, map[string]any{"expr": "index-get", "base": base, "index": idx}), nil
	case *ast.SliceExpr:
		base, err := b.value(v.X)
		if err != nil {
			return nil, err
		}
		low := any(map[string]any{"expr": "int", "value": "0", "type": intType("int")})
		if v.Low != nil {
			if low, err = b.value(v.Low); err != nil {
				return nil, err
			}
		}
		var high any
		if v.High != nil {
			if high, err = b.value(v.High); err != nil {
				return nil, err
			}
		} else {
			opTy, err := e.typeOf(v.X)
			if err != nil {
				return nil, err
			}
			high = map[string]any{"expr": "builtin-len", "operand": base, "operandType": opTy}
		}
		head := map[string]any{"expr": "slice", "base": base, "low": low, "high": high}
		if v.Slice3 && v.Max != nil {
			m, err := b.value(v.Max)
			if err != nil {
				return nil, err
			}
			head["max"] = m
		}
		ty, err := e.typeOf(v)
		if err != nil {
			return nil, err
		}
		return b.evalOcc("slice", ty, head), nil
	case *ast.CallExpr:
		slots, err := b.call(v, 1)
		if err != nil {
			return nil, err
		}
		if len(slots) != 1 {
			return nil, unsup("unseq lowering: call in value position with %d results", len(slots))
		}
		return slots[0], nil
	case *ast.BinaryExpr:
		op, ok := binaryOp(v.Op)
		if !ok {
			return nil, unsup("unseq lowering: binary operator %s", v.Op)
		}
		if op == "&&" || op == "||" {
			return b.guard(v, op)
		}
		l, err := b.value(v.X)
		if err != nil {
			return nil, err
		}
		r, err := b.value(v.Y)
		if err != nil {
			return nil, err
		}
		head := map[string]any{"expr": "binary", "op": op, "x": l, "y": r}
		if isComparison(op) {
			oty, err := e.typeOf(v.X)
			if err != nil {
				return nil, err
			}
			head["operandType"] = oty
		}
		ty, err := e.typeOf(v)
		if err != nil {
			return nil, err
		}
		return b.evalOcc("op", ty, head), nil
	case *ast.UnaryExpr:
		var op string
		switch v.Op {
		case token.SUB:
			op = "-"
		case token.NOT:
			op = "!"
		case token.XOR:
			op = "^"
		default:
			return nil, unsup("unseq lowering: unary operator %s", v.Op)
		}
		x, err := b.value(v.X)
		if err != nil {
			return nil, err
		}
		ty, err := e.typeOf(v)
		if err != nil {
			return nil, err
		}
		return b.evalOcc("op", ty, map[string]any{"expr": "unary", "op": op, "x": x}), nil
	case *ast.SelectorExpr:
		// Stage E E1: `pkg.V`, a source-package qualified package-level
		// variable — the same READ occurrence as the unqualified spelling.
		pkgName, ok := e.qualifiedPkgRef(v)
		if !ok {
			return nil, unsup("unseq lowering: selector %s outside the admitted grammar", v.Sel.Name)
		}
		w, err := e.emitQualifiedSelector(v, pkgName)
		if err != nil {
			return nil, err
		}
		m, isMap := w.(map[string]any)
		if !isMap || m["expr"] != "deref" {
			return nil, unsup("unseq lowering: qualified package-level variable %s did not lower to a global read (%v) — outside the admitted grammar", v.Sel.Name, w)
		}
		ty, err := e.typeOf(v)
		if err != nil {
			return nil, err
		}
		m["type"] = ty
		return b.evalOcc("read", ty, m), nil
	case *ast.TypeAssertExpr:
		operand, err := b.value(v.X)
		if err != nil {
			return nil, err
		}
		target, err := e.emitType(e.goTypeOf(v.Type))
		if err != nil {
			return nil, err
		}
		source, err := e.emitType(e.goTypeOf(v.X))
		if err != nil {
			return nil, err
		}
		return b.evalOcc("assert", target, map[string]any{"expr": "type-assert", "operand": operand,
			"target": target, "source": source}), nil
	}
	return nil, unsup("unseq lowering: expression %T outside the admitted grammar", x)
}

// call lowers a call (a non-constant len/cap, a same-package function, a
// func-typed local, an immediately-invoked literal): the callee value and the
// arguments first (post-order, inside the event subtree), then the invocation
// with `after` = the E1 anchor. Returns the result slots (0..maxResults).
func (b *unseqBuilder) call(c *ast.CallExpr, maxResults int) ([]any, error) {
	e := b.e
	b.push()
	popped := false
	defer func() {
		if !popped {
			b.frames = b.frames[:len(b.frames)-1]
		}
	}()
	if id, ok := ast.Unparen(c.Fun).(*ast.Ident); ok {
		if _, isBuiltin := e.info.Uses[id].(*types.Builtin); isBuiltin {
			switch id.Name {
			case "len", "cap":
				operand, err := b.value(c.Args[0])
				if err != nil {
					return nil, err
				}
				opTy, err := e.typeOf(c.Args[0])
				if err != nil {
					return nil, err
				}
				tag := "builtin-len"
				if id.Name == "cap" {
					tag = "builtin-cap"
				}
				cell := b.newCell(intType("int"))
				name := b.occName(id.Name)
				o := map[string]any{"name": name, "kind": "eval", "bind": cell,
					"head": map[string]any{"expr": tag, "operand": operand, "operandType": opTy, "type": intType("int")}}
				if after := b.eventAfter(); after != nil {
					o["after"] = after
				}
				if b.region != "" {
					o["region"] = b.region
				}
				block := append(b.pop(), o)
				popped = true
				b.emitEventBlock(block)
				b.anchor = name
				return []any{slotIdent(cell, intType("int"))}, nil
			}
			return nil, unsup("unseq lowering: builtin %s", id.Name)
		}
	}
	// the callee VALUE
	var callee any
	var sig *types.Signature
	switch fn := ast.Unparen(c.Fun).(type) {
	case *ast.Ident:
		switch obj := e.info.Uses[fn].(type) {
		case *types.Func:
			sig, _ = obj.Type().(*types.Signature)
			callee = map[string]any{"expr": "func-value", "func": e.funcWireName(obj), "captured": []any{}}
		case *types.Var:
			sig, _ = types.Unalias(obj.Type()).Underlying().(*types.Signature)
			w, err := b.value(fn)
			if err != nil {
				return nil, err
			}
			callee = w
		default:
			return nil, unsup("unseq lowering: callee %s", fn.Name)
		}
	case *ast.FuncLit:
		sig, _ = e.goTypeOf(fn).(*types.Signature)
		w, err := e.emitFuncLit(fn)
		if err != nil {
			return nil, err
		}
		callee = w
	default:
		return nil, unsup("unseq lowering: callee %T", c.Fun)
	}
	if sig == nil {
		return nil, unsup("unseq lowering: callee without a signature")
	}
	// the arguments (atoms, boxed where the parameter is interface-typed)
	args := []any{}
	for i, a := range c.Args {
		w, err := b.value(a)
		if err != nil {
			return nil, err
		}
		w, err = e.wrapInterfaceConversion(sig.Params().At(i).Type(), e.goTypeOf(a), w)
		if err != nil {
			return nil, err
		}
		args = append(args, w)
	}
	resultTypes, err := e.emitResultTypes(sig)
	if err != nil {
		return nil, err
	}
	if len(resultTypes) > maxResults {
		return nil, unsup("unseq lowering: %d results in a position admitting %d", len(resultTypes), maxResults)
	}
	binds := []any{}
	slots := []any{}
	for _, rt := range resultTypes {
		cell := b.newCell(rt)
		binds = append(binds, cell)
		slots = append(slots, slotIdent(cell, rt))
	}
	name := b.occName("call")
	o := map[string]any{"name": name, "kind": "invoke", "binds": binds, "callee": callee,
		"args": args, "resultTypes": resultTypes}
	if after := b.eventAfter(); after != nil {
		o["after"] = after
	}
	if b.region != "" {
		o["region"] = b.region
	}
	block := append(b.pop(), o)
	popped = true
	b.emitEventBlock(block)
	b.anchor = name
	return slots, nil
}

// guard lowers `l && r` / `l || r` (v2.1 §1 G, review R2): the left operand's
// occurrences, the guard ENTRY (after the current anchor — E1 at the entry for
// earlier events) testing the left's cell, the right operand inside the region
// with a fresh anchor, the COMPLETION producing the logical result in the region;
// the anchor becomes the completion (E1 at the completion for later events).
func (b *unseqBuilder) guard(v *ast.BinaryExpr, op string) (any, error) {
	boolTy := map[string]any{"kind": "bool"}
	// the LEFT operand: its occurrences sit right before the guard (legacy's
	// `$c := lhs` at the guard's hoist position)
	b.push()
	left, err := b.value(v.X)
	if err != nil {
		b.frames = b.frames[:len(b.frames)-1]
		return nil, err
	}
	test, _ := b.ensureCell(left, boolTy)
	leftBlock := b.pop()
	out := b.newCell(boolTy)
	gname := b.occName("guard")
	g := map[string]any{"name": gname, "kind": "guard", "test": test, "when": op == "&&", "out": out}
	if after := b.eventAfter(); after != nil {
		g["after"] = after
	}
	if b.region != "" {
		g["region"] = b.region
	}
	// the RIGHT operand: its own frame, inside the region, with a fresh anchor
	savedAnchor, savedRegion := b.anchor, b.region
	b.anchor, b.region = "", gname
	b.push()
	right, err := b.value(v.Y)
	if err != nil {
		b.frames = b.frames[:len(b.frames)-1]
		b.anchor, b.region = savedAnchor, savedRegion
		return nil, err
	}
	head := map[string]any{}
	for k, val := range right.(map[string]any) {
		head[k] = val
	}
	head["type"] = boolTy
	jname := b.occName("join")
	b.emit(map[string]any{"name": jname, "kind": "eval", "bind": out, "head": head})
	regionBlock := b.pop()
	b.region = savedRegion
	b.anchor = jname
	block := append(append(leftBlock, g), regionBlock...)
	b.emitEventBlock(block)
	return slotIdent(out, boolTy), nil
}

// elemTarget lowers a slice-element target plan `a[i]` on FROZEN atoms and
// returns its binder.
func (b *unseqBuilder) elemTarget(ix *ast.IndexExpr) (string, error) {
	base, err := b.value(ix.X)
	if err != nil {
		return "", err
	}
	idx, err := b.value(ix.Index)
	if err != nil {
		return "", err
	}
	t := b.newTargetBinder()
	b.emit(map[string]any{"name": b.occName("target"), "kind": "target", "bind": t,
		"lhs": map[string]any{"target": "addr", "expr": map[string]any{"expr": "index-addr", "base": base, "index": idx}}})
	return t, nil
}

func (b *unseqBuilder) node(then any) map[string]any {
	occs := append(append([]any{}, b.frames[0].events...), b.frames[0].residual...)
	stores := b.stores
	if stores == nil {
		stores = []any{}
	}
	cells := b.cells
	if cells == nil {
		cells = []any{}
	}
	return map[string]any{"stmt": "unseq", "cells": cells, "occs": occs, "stores": stores, "then": then}
}

func emptyBlock() map[string]any { return map[string]any{"stmt": "block", "body": []any{}} }

// synthOne is the `1` of `x++`/`x--` at the operand's integer kind (emitIncDec's rule).
func (e *emitter) synthOne(t types.Type) (any, error) {
	if bt, ok := types.Unalias(t).Underlying().(*types.Basic); ok && bt.Info()&types.IsInteger != 0 {
		vt, err := e.emitBasic(bt)
		if err != nil {
			return nil, err
		}
		return map[string]any{"expr": "int", "value": "1", "type": vt}, nil
	}
	return nil, unsup("unseq lowering: ++/-- on a non-integer operand")
}

// emitUnseqSweep lowers ONE admitted sweep to an `unseq` statement node.
func (e *emitter) emitUnseqSweep(s ast.Stmt, ctx *unseqCtx) (any, error) {
	savedHoisted := len(e.hoisted)
	e.probeSuppress++
	defer func() { e.probeSuppress-- }()
	b := e.newUnseqBuilder(ctx)
	var then any
	switch st := s.(type) {
	case *ast.AssignStmt:
		switch st.Tok {
		case token.DEFINE, token.ASSIGN:
			define := st.Tok == token.DEFINE
			switch l := ast.Unparen(st.Lhs[0]).(type) {
			case *ast.Ident, *ast.SelectorExpr:
				// a local (`x := e`, `x = e`) or — Stage E E1 — a package-level
				// variable (`g = e`, `pkg.V = e`): a plan with no operands; the
				// store rides `then` (emitAssignTargetPhase1 spells both).
				v, err := b.value(st.Rhs[0])
				if err != nil {
					return nil, err
				}
				v, err = e.wrapInterfaceConversion(e.assignTargetType(l, define), e.goTypeOf(st.Rhs[0]), v)
				if err != nil {
					return nil, err
				}
				lhs, err := e.emitAssignTargetPhase1(l, define)
				if err != nil {
					return nil, err
				}
				then = map[string]any{"stmt": "assign", "define": define, "lhs": []any{lhs}, "rhs": []any{v}}
			case *ast.IndexExpr:
				t, err := b.elemTarget(l)
				if err != nil {
					return nil, err
				}
				v, err := b.value(st.Rhs[0])
				if err != nil {
					return nil, err
				}
				elemTy, err := e.typeOf(l)
				if err != nil {
					return nil, err
				}
				cell, _ := b.ensureCell(v, elemTy)
				b.stores = append(b.stores, map[string]any{"target": t, "value": cell})
				then = emptyBlock()
			default:
				return nil, unsup("unseq lowering: assignment target %T", st.Lhs[0])
			}
		default:
			op, ok := compoundOp(st.Tok)
			if !ok {
				return nil, unsup("unseq lowering: assignment operator %s", st.Tok)
			}
			var err error
			then, err = b.readWrite(st.Lhs[0], op, func() (any, error) { return b.value(st.Rhs[0]) })
			if err != nil {
				return nil, err
			}
		}
	case *ast.IncDecStmt:
		op := "+"
		if st.Tok == token.DEC {
			op = "-"
		}
		var err error
		then, err = b.readWrite(st.X, op, func() (any, error) { return e.synthOne(e.goTypeOf(st.X)) })
		if err != nil {
			return nil, err
		}
	case *ast.ReturnStmt:
		results := []any{}
		if len(st.Results) == 1 {
			if call, isCall := ast.Unparen(st.Results[0]).(*ast.CallExpr); isCall {
				if tup, isTup := e.goTypeOf(call).(*types.Tuple); isTup {
					slots, err := b.call(call, 2)
					if err != nil {
						return nil, err
					}
					for i, sl := range slots {
						w, err := e.wrapInterfaceConversion(e.curResults.At(i).Type(), tup.At(i).Type(), sl)
						if err != nil {
							return nil, err
						}
						results = append(results, w)
					}
					then = map[string]any{"stmt": "return", "results": results}
				}
			}
		}
		if then == nil {
			for i, r := range st.Results {
				w, err := b.value(r)
				if err != nil {
					return nil, err
				}
				if e.curResults != nil && i < e.curResults.Len() {
					w, err = e.wrapInterfaceConversion(e.curResults.At(i).Type(), e.goTypeOf(r), w)
					if err != nil {
						return nil, err
					}
				}
				results = append(results, w)
			}
			then = map[string]any{"stmt": "return", "results": results}
		}
	case *ast.ExprStmt:
		call := ast.Unparen(st.X).(*ast.CallExpr)
		if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
			if _, isBuiltin := e.info.Uses[id].(*types.Builtin); isBuiltin && (id.Name == "print" || id.Name == "println") {
				args := []any{}
				for _, a := range call.Args {
					w, err := b.value(a)
					if err != nil {
						return nil, err
					}
					args = append(args, w)
				}
				then = map[string]any{"stmt": "print", "newline": id.Name == "println", "args": args}
			}
		}
		if then == nil {
			if _, err := b.call(call, 2); err != nil { // results, if any, land in discard cells
				return nil, err
			}
			then = emptyBlock()
		}
	default:
		return nil, unsup("unseq lowering: statement %T", s)
	}
	if len(e.hoisted) != savedHoisted {
		return nil, unsup("unseq lowering produced a legacy hoist — a sweep is ONE unseq graph or the legacy path, never a mixture (v2.1 §3.7); refused by name")
	}
	return b.node(then), nil
}

// readWrite lowers `lv op= rhs` (and `lv++`): a slice element → target plan +
// load + op + store; a local → the read (an occurrence when address-taken, the
// bare ident when private) + op, the store in `then`; a package-level variable
// (Stage E E1; `g` or `pkg.V`) → its READ occurrence + op, the store in `then`
// through the same operand-free identity (`addr(globaladdr)`).
func (b *unseqBuilder) readWrite(lv ast.Expr, op string, rhs func() (any, error)) (any, error) {
	e := b.e
	switch l := ast.Unparen(lv).(type) {
	case *ast.IndexExpr:
		t, err := b.elemTarget(l)
		if err != nil {
			return nil, err
		}
		elemTy, err := e.typeOf(l)
		if err != nil {
			return nil, err
		}
		rd := b.newCell(elemTy)
		b.emit(map[string]any{"name": b.occName("load"), "kind": "load", "bind": rd, "target": t})
		r, err := rhs()
		if err != nil {
			return nil, err
		}
		res := b.evalOcc("op", elemTy, map[string]any{"expr": "binary", "op": op, "x": slotIdent(rd, elemTy), "y": r})
		b.stores = append(b.stores, map[string]any{"target": t, "value": res.(map[string]any)["name"]})
		return emptyBlock(), nil
	case *ast.Ident, *ast.SelectorExpr:
		x, err := b.value(l) // a READ occurrence when address-taken or package-level, the bare ident when private
		if err != nil {
			return nil, err
		}
		r, err := rhs()
		if err != nil {
			return nil, err
		}
		ty, err := e.typeOf(l)
		if err != nil {
			return nil, err
		}
		res := b.evalOcc("op", ty, map[string]any{"expr": "binary", "op": op, "x": x, "y": r})
		lhs, err := e.emitAssignTargetPhase1(l, false)
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "assign", "define": false, "lhs": []any{lhs}, "rhs": []any{res}}, nil
	}
	return nil, unsup("unseq lowering: read-write target %T", lv)
}
