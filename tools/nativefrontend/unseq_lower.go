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
// STAGE E E2 (pointers, fields, maps). `*p` → `eval deref(ptr atom)`; `p.f` →
// `eval field-get(deref(ptr atom))`, `s.f` → `eval field-get(base atom or slot)`
// (an address-taken struct local's read is FUSED with the selection: one read
// occurrence, no struct-typed cell); `m[k]` → `eval map-get(base atom, key atom)`.
// Targets: `*p` → `target $t addr(ptr atom)` (the pointer VALUE frozen), `p.f` /
// `s.f` → `target $t addr(field-addr(ptr atom | ref s | globaladdr))`, `m[k]` →
// `target $t map(base atom, key atom, keyType, valueType)` (the map VALUE and key
// VALUE frozen — `Assignee.mapElem`); the compound forms load through the plan
// and store through the same plan.
//
// STAGE E E3 (receives, method calls). `<-ch` → a `recv` occurrence (kind
// "recv": the binder cell, the channel atom, the element type; E1 `after` like
// a call — the machine runs `Stmt.chanRecv` with the cell as its target). A
// method call `x.M(args)` → an `invoke` whose callee is `func-value{methodFuncKey}`
// and whose first argument is the receiver sub-evaluation: the pointer atom,
// `ref x` (an addressable variable's address — admitted as a frozen-address
// argument), `eval addr-of-deref(p)` (for `(*p).M()`), the value atom / read, or
// `eval deref(p)` (a value receiver through a pointer).
//
// STAGE E E4 (conversions, allocations). A conversion `T(x)` → a pure `eval` head
// over the operand's atom — emitCallNode's own operator table (`convert`,
// `bytes-from-string`, `string-from-bytes`, `runes-from-string`,
// `string-from-runes`, `string-from-rune`; a bool retyping is the operand). A
// VALUE struct literal `T{…}` → `eval struct-lit(payloads)` (the emitter's own
// shape: fields in declaration order, omitted fields `default`, interface-typed
// fields boxed). `&T{…}` → an `allocate` body `new(struct-lit, T)` and a slice
// literal → an `allocate` body `slice-lit(elem, length, elems)`, both in the
// RESIDUAL (no E1 edge — v2.1 R3: a composite literal is not a call; BUG-102's
// evidence, gc leaves it in the residual after the call temps). `make(…)` /
// `new(T)` → an `allocate` body (`make-slice` / `make-map` / `make-chan` / `new`)
// as an E1-ordered EVENT with the anchor, like len/cap (spec#Built-in_functions;
// the machine's hoist and gc's agree — BUG-062 / FR-28's rows).
//
// THE MIXTURE GUARD. The lowering runs with `probeSuppress` raised and asserts the
// hoist accumulator unchanged afterwards: a legacy hoist or probe produced inside
// a graph lowering is refused by name (v2.1 §3.7: never a mixture).

import (
	"go/ast"
	"go/constant"
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
		if mt, isMap := types.Unalias(e.goTypeOf(v.X)).Underlying().(*types.Map); isMap {
			// Stage E E2: ONE map read on the frozen base and key values.
			kt, err := e.emitType(mt.Key())
			if err != nil {
				return nil, err
			}
			vt, err := e.emitType(mt.Elem())
			if err != nil {
				return nil, err
			}
			return b.evalOcc("mapread", ty, map[string]any{"expr": "map-get", "base": base, "index": idx,
				"keyType": kt, "valueType": vt}), nil
		}
		return b.evalOcc("access", ty, map[string]any{"expr": "index-get", "base": base, "index": idx}), nil
	case *ast.StarExpr:
		// Stage E E2: `*p` — the dereference is ONE occurrence on the pointer value.
		ptr, err := b.value(v.X)
		if err != nil {
			return nil, err
		}
		ty, err := e.typeOf(v)
		if err != nil {
			return nil, err
		}
		return b.evalOcc("deref", ty, map[string]any{"expr": "deref", "ptr": ptr, "type": ty}), nil
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
		if tv, ok := e.info.Types[v.Fun]; ok && tv.IsType() {
			return b.conv(v) // Stage E E4: a conversion is a pure head
		}
		slots, err := b.call(v, 1)
		if err != nil {
			return nil, err
		}
		if len(slots) != 1 {
			return nil, unsup("unseq lowering: call in value position with %d results", len(slots))
		}
		return slots[0], nil
	case *ast.CompositeLit:
		return b.compositeLit(v) // Stage E E4
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
		if v.Op == token.ARROW {
			return b.recv(v)
		}
		if v.Op == token.AND {
			// Stage E E4: `&T{…}` — the struct literal's payloads, then an `allocate` body (`new`).
			cl, isLit := ast.Unparen(v.X).(*ast.CompositeLit)
			if !isLit {
				return nil, unsup("unseq lowering: address of a non-literal operand")
			}
			return b.addrLit(cl, v)
		}
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
			// Stage E E2: a FIELD read — ONE occurrence: `field-get(deref(ptr))` through a
			// pointer (nil check + load), `field-get(base)` on a struct value (an
			// address-taken struct local's read fused with the selection; a private
			// local an atom; a nested base a slot).
			recv, structName, err := b.fieldRecv(v)
			if err != nil {
				return nil, err
			}
			ty, err := e.typeOf(v)
			if err != nil {
				return nil, err
			}
			return b.evalOcc("field", ty, map[string]any{"expr": "field-get", "recv": recv, "typeId": structName,
				"field": v.Sel.Name}), nil
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
			case "make", "new":
				// Stage E E4: the allocation call — its size operands inside this frame,
				// then the `alloc` body as an E1-ordered event (the frame is popped there).
				slot, err := b.makeNew(c, id.Name)
				if err != nil {
					return nil, err
				}
				popped = true
				return []any{slot}, nil
			case "min", "max":
				// Stage E5 E5a: a pure E1-ordered head over the operand atoms (Expr.minOf/maxOf),
				// its block like len/cap's: the operands, then the event with the anchor.
				args := []any{}
				for _, a := range c.Args {
					w, err := b.value(a)
					if err != nil {
						return nil, err
					}
					args = append(args, w)
				}
				ty, err := e.typeOf(c)
				if err != nil {
					return nil, err
				}
				cell := b.newCell(ty)
				name := b.occName(id.Name)
				o := map[string]any{"name": name, "kind": "eval", "bind": cell,
					"head": map[string]any{"expr": id.Name, "args": args, "type": ty}}
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
				return []any{slotIdent(cell, ty)}, nil
			case "append":
				// Stage E5 E5a: the effectful append as a `wide` body (the frame is popped there).
				slot, err := b.wideAppend(c)
				if err != nil {
					return nil, err
				}
				popped = true
				return []any{slot}, nil
			case "copy":
				slot, err := b.wideCopy(c)
				if err != nil {
					return nil, err
				}
				popped = true
				return []any{slot}, nil
			}
			return nil, unsup("unseq lowering: builtin %s", id.Name)
		}
	}
	// the callee VALUE
	var callee any
	var sig *types.Signature
	var recvArg any // Stage E E3: a method call's receiver argument (nil for a function)
	switch fn := ast.Unparen(c.Fun).(type) {
	case *ast.SelectorExpr:
		// Stage E E3: a method call on a concrete receiver — the callee is the
		// method's function value, the receiver its first argument.
		r, key, s, err := b.methodCallee(fn)
		if err != nil {
			return nil, err
		}
		recvArg, sig = r, s
		callee = map[string]any{"expr": "func-value", "func": key, "captured": []any{}}
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
	if recvArg != nil {
		args = append(args, recvArg)
	}
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

// conv lowers a conversion T(x) (Stage E E4) as a PURE OP head over the operand's
// atom, mirroring emitCallNode's operator table: the byte/rune/string forms have
// their own machine operators, a bool retyping is the operand itself, the generic
// `convert` covers the scalar conversions.
func (b *unseqBuilder) conv(c *ast.CallExpr) (any, error) {
	e := b.e
	arg, err := b.value(c.Args[0])
	if err != nil {
		return nil, err
	}
	tt := types.Unalias(e.goTypeOf(c)).Underlying()
	ot := types.Unalias(e.goTypeOf(c.Args[0])).Underlying()
	ty, err := e.typeOf(c)
	if err != nil {
		return nil, err
	}
	var head map[string]any
	switch {
	case isByteSlice(tt) && isStringType(ot):
		head = map[string]any{"expr": "bytes-from-string", "x": arg}
	case isStringType(tt) && isByteSlice(ot):
		head = map[string]any{"expr": "string-from-bytes", "x": arg}
	case isRuneSlice(tt) && isStringType(ot):
		head = map[string]any{"expr": "runes-from-string", "x": arg}
	case isStringType(tt) && isRuneSlice(ot):
		head = map[string]any{"expr": "string-from-runes", "x": arg}
	}
	if head == nil {
		if tb, ok := tt.(*types.Basic); ok {
			if ob, isOB := ot.(*types.Basic); isOB {
				if tb.Kind() == types.Bool && ob.Kind() == types.Bool {
					return arg, nil // a static retyping: no machine op (emitCallNode)
				}
				if tb.Info()&types.IsString != 0 && ob.Info()&types.IsInteger != 0 {
					head = map[string]any{"expr": "string-from-rune", "x": arg}
				}
			}
		}
	}
	if head == nil {
		target, err := e.emitType(e.goTypeOf(c))
		if err != nil {
			return nil, err
		}
		head = map[string]any{"expr": "convert", "target": target, "x": arg}
	}
	return b.evalOcc("conv", ty, head), nil
}

// structLitHead lowers a VALUE struct literal `T{…}` (Stage E E4) to the emitter's
// own `struct-lit` shape over PAYLOADS (atoms / boxed atoms / zero values), the
// fields in declaration order; the element values are lowered in SOURCE order
// (their calls are E1-ordered events; the head consumes their cells).
func (b *unseqBuilder) structLitHead(cl *ast.CompositeLit) (map[string]any, error) {
	e := b.e
	t := e.goTypeOf(cl)
	st, isStruct := types.Unalias(t).Underlying().(*types.Struct)
	if !isStruct {
		return nil, unsup("unseq lowering: struct literal of a non-struct type %s", t)
	}
	target, err := e.emitType(t)
	if err != nil {
		return nil, err
	}
	keyed := map[string]any{}
	keyedTypes := map[string]types.Type{}
	positional := []any{}
	positionalTypes := []types.Type{}
	for _, elt := range cl.Elts {
		if kv, ok := elt.(*ast.KeyValueExpr); ok {
			w, err := b.value(kv.Value)
			if err != nil {
				return nil, err
			}
			name := kv.Key.(*ast.Ident).Name
			keyed[name] = w
			keyedTypes[name] = e.goTypeOf(kv.Value)
			continue
		}
		w, err := b.value(elt)
		if err != nil {
			return nil, err
		}
		positional = append(positional, w)
		positionalTypes = append(positionalTypes, e.goTypeOf(elt))
	}
	args := []any{}
	for i := 0; i < st.NumFields(); i++ {
		fld := st.Field(i)
		if len(positional) > 0 {
			if i >= len(positional) {
				return nil, unsup("unseq lowering: positional struct literal missing field %s", fld.Name())
			}
			w, err := e.wrapInterfaceConversion(fld.Type(), positionalTypes[i], positional[i])
			if err != nil {
				return nil, err
			}
			args = append(args, w)
			continue
		}
		if w, ok := keyed[fld.Name()]; ok {
			w, err := e.wrapInterfaceConversion(fld.Type(), keyedTypes[fld.Name()], w)
			if err != nil {
				return nil, err
			}
			args = append(args, w)
			continue
		}
		fty, err := e.emitType(fld.Type())
		if err != nil {
			return nil, err
		}
		args = append(args, map[string]any{"expr": "default", "type": fty})
	}
	return map[string]any{"expr": "struct-lit", "target": target, "args": args}, nil
}

// compositeLit lowers a VALUE composite literal (Stage E E4): a struct literal as a
// pure `struct-lit` head (one `eval` occurrence), a slice literal as an `allocate`
// body (a fresh backing array — NO E1 edge, v2.1 R3) in the residual.
func (b *unseqBuilder) compositeLit(cl *ast.CompositeLit) (any, error) {
	e := b.e
	t := e.goTypeOf(cl)
	ty, err := e.typeOf(cl)
	if err != nil {
		return nil, err
	}
	switch u := types.Unalias(t).Underlying().(type) {
	case *types.Struct:
		head, err := b.structLitHead(cl)
		if err != nil {
			return nil, err
		}
		return b.evalOcc("lit", ty, head), nil
	case *types.Slice:
		elemTy, err := e.emitType(u.Elem())
		if err != nil {
			return nil, err
		}
		elems := []any{}
		idx, length := int64(0), int64(0)
		for _, elt := range cl.Elts {
			val := elt
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				tv, isConst := e.info.Types[kv.Key]
				if !isConst || tv.Value == nil {
					return nil, unsup("unseq lowering: slice literal key is not constant")
				}
				idx, _ = constant.Int64Val(tv.Value)
				val = kv.Value
			}
			w, err := b.value(val)
			if err != nil {
				return nil, err
			}
			w, err = e.wrapInterfaceConversion(u.Elem(), e.goTypeOf(val), w)
			if err != nil {
				return nil, err
			}
			elems = append(elems, map[string]any{"index": idx, "value": w})
			if idx+1 > length {
				length = idx + 1
			}
			idx++
		}
		spec := map[string]any{"stmt": "slice-lit", "elem": elemTy, "length": length, "elems": elems}
		return b.allocOcc("lit", ty, spec, false), nil
	case *types.Map:
		// Stage E5 E5c: the map literal as an `allocate` body (`map-lit`: the fresh map + the keyed
		// entry stores, in source order) in the residual — no E1 edge.
		kt, err := e.emitType(u.Key())
		if err != nil {
			return nil, err
		}
		vt, err := e.emitType(u.Elem())
		if err != nil {
			return nil, err
		}
		entries := []any{}
		for _, elt := range cl.Elts {
			kv, ok := elt.(*ast.KeyValueExpr)
			if !ok {
				return nil, unsup("unseq lowering: map literal element without a key")
			}
			k, err := b.value(kv.Key)
			if err != nil {
				return nil, err
			}
			v, err := b.value(kv.Value)
			if err != nil {
				return nil, err
			}
			v, err = e.wrapInterfaceConversion(u.Elem(), e.goTypeOf(kv.Value), v)
			if err != nil {
				return nil, err
			}
			entries = append(entries, map[string]any{"key": k, "value": v})
		}
		spec := map[string]any{"stmt": "map-lit", "keyType": kt, "valueType": vt, "entries": entries}
		return b.allocOcc("lit", ty, spec, false), nil
	}
	return nil, unsup("unseq lowering: composite literal of type %s", t)
}

// addrLit lowers `&T{…}` (Stage E E4): the struct literal's payloads, then an
// `allocate` body (`new`) binding the fresh pointer (no E1 edge).
func (b *unseqBuilder) addrLit(cl *ast.CompositeLit, u *ast.UnaryExpr) (any, error) {
	e := b.e
	head, err := b.structLitHead(cl)
	if err != nil {
		return nil, err
	}
	elemTy, err := e.emitType(e.goTypeOf(cl))
	if err != nil {
		return nil, err
	}
	ty, err := e.typeOf(u)
	if err != nil {
		return nil, err
	}
	return b.allocOcc("new", ty, map[string]any{"stmt": "new", "value": head, "elemType": elemTy}, false), nil
}

// makeNew lowers `make(T, …)` / `new(T)` / `new(x)` (Stage E E4) inside the
// call's operand frame (pushed by `call`): the size operands — or Go 1.26
// `new(x)`'s argument — as atoms, then the `allocate` body as an E1-ordered
// EVENT after the anchor (the anchor moves to it) — a function call like
// len/cap; the frame is popped into the event block. `new(x)`'s allocation
// stores the argument's value (the audit's F1, 2026-09-21: the first cut
// emitted the zero value for every `new`, dropping the initializer and any
// call inside it — the legacy arm in emit.go had the value form since Go 1.26).
func (b *unseqBuilder) makeNew(c *ast.CallExpr, name string) (any, error) {
	e := b.e
	t := e.goTypeOf(c)
	ty, err := e.typeOf(c)
	if err != nil {
		return nil, err
	}
	var spec map[string]any
	if name == "new" {
		pt, isPtr := types.Unalias(t).Underlying().(*types.Pointer)
		if !isPtr {
			return nil, unsup("unseq lowering: new without a pointer result")
		}
		elemTy, err := e.emitType(pt.Elem())
		if err != nil {
			return nil, err
		}
		val := map[string]any{"expr": "default", "type": elemTy}
		if tv, ok := e.info.Types[c.Args[0]]; !ok || !tv.IsType() {
			// new(x): the argument's VALUE — a slot, a private local or a constant
			// (its occurrences land in this frame, before the allocate event).
			w, err := b.value(c.Args[0])
			if err != nil {
				return nil, err
			}
			w, err = e.wrapInterfaceConversion(pt.Elem(), e.goTypeOf(c.Args[0]), w)
			if err != nil {
				return nil, err
			}
			m, ok := w.(map[string]any)
			if !ok {
				return nil, unsup("unseq lowering: new operand emission shape (%T)", w)
			}
			val = m
		}
		spec = map[string]any{"stmt": "new", "value": val, "elemType": elemTy}
	} else {
		operands := []any{}
		for _, a := range c.Args[1:] {
			w, err := b.value(a)
			if err != nil {
				return nil, err
			}
			operands = append(operands, w)
		}
		switch u := types.Unalias(t).Underlying().(type) {
		case *types.Slice:
			elemTy, err := e.emitType(u.Elem())
			if err != nil {
				return nil, err
			}
			if len(operands) < 1 {
				return nil, unsup("unseq lowering: make of a slice without a length")
			}
			spec = map[string]any{"stmt": "make-slice", "elem": elemTy, "len": operands[0]}
			if len(operands) >= 2 {
				spec["cap"] = operands[1]
			}
		case *types.Map:
			keyTy, err := e.emitType(u.Key())
			if err != nil {
				return nil, err
			}
			valTy, err := e.emitType(u.Elem())
			if err != nil {
				return nil, err
			}
			spec = map[string]any{"stmt": "make-map", "keyType": keyTy, "valueType": valTy}
			if len(operands) >= 1 {
				spec["hint"] = operands[0]
			}
		case *types.Chan:
			elemTy, err := e.emitType(u.Elem())
			if err != nil {
				return nil, err
			}
			spec = map[string]any{"stmt": "make-chan", "elem": elemTy}
			if len(operands) >= 1 {
				spec["cap"] = operands[0]
			}
		default:
			return nil, unsup("unseq lowering: make of %s", t)
		}
	}
	return b.allocOcc(name, ty, spec, true), nil
}

// isBlankTarget: the blank identifier `_`.
func isBlankTarget(l ast.Expr) bool {
	id, ok := ast.Unparen(l).(*ast.Ident)
	return ok && id.Name == "_"
}

// varTarget lowers a PLAIN variable target as a `target` plan on its own address
// (E5b: a plain target beside a planned sibling rides the same phase-2 store list;
// the plan checks nothing and reads nothing) and returns its binder.
func (b *unseqBuilder) varTarget(id *ast.Ident) string {
	t := b.newTargetBinder()
	b.emit(map[string]any{"name": b.occName("target"), "kind": "target", "bind": t,
		"lhs": map[string]any{"target": "var", "id": b.e.localRename(b.e.info.Uses[id], id.Name)}})
	return t
}

// multiAssign lowers a MULTI-TARGET assignment (Stage E5 E5b): phase 1 — the
// right-hand values (a tuple's expressions; a multi-value call's two results; a
// comma-ok receive's two binders; a comma-ok map lookup / type assertion as a
// two-binder `wide` occurrence in the residual — a read / a pure op, never an
// event); phase 2 — when some target is PLANNED, every non-blank target is a
// `target` plan (siblings) and the stores ride `stores` left to right; otherwise
// (plain / global / blank targets only) the multi-assign rides `then` — the
// legacy `assign` shape with declares, blank discards and the interface boxing
// wraps, whose plain-variable stores never fail.
func (b *unseqBuilder) multiAssign(st *ast.AssignStmt) (any, error) {
	e := b.e
	define := st.Tok == token.DEFINE
	// phase 1, in SOURCE order: the targets' operands first (a call inside a target's
	// index precedes the right-hand side's events — spec#Order_of_evaluation; the spec's
	// own `y[f()], ok = g(…), k()` traces f before g and k), then the right-hand values
	prepared := map[int]*preparedTarget{}
	for i, l := range st.Lhs {
		if b.isPlannedTarget(l) {
			p, err := b.prepareTarget(l)
			if err != nil {
				return nil, err
			}
			prepared[i] = p
		}
	}
	var vals []any
	var valTys []types.Type
	if len(st.Rhs) == 1 && len(st.Lhs) == 2 {
		switch r := ast.Unparen(st.Rhs[0]).(type) {
		case *ast.UnaryExpr:
			if r.Op == token.ARROW {
				slots, elemGo, err := b.recvN(r, 2)
				if err != nil {
					return nil, err
				}
				vals, valTys = slots, []types.Type{elemGo, types.Typ[types.Bool]}
			}
		case *ast.IndexExpr:
			if mt, isMap := types.Unalias(e.goTypeOf(r.X)).Underlying().(*types.Map); isMap {
				base, err := b.value(r.X)
				if err != nil {
					return nil, err
				}
				idx, err := b.value(r.Index)
				if err != nil {
					return nil, err
				}
				kt, err := e.emitType(mt.Key())
				if err != nil {
					return nil, err
				}
				vt, err := e.emitType(mt.Elem())
				if err != nil {
					return nil, err
				}
				vals = b.wideOcc("lookup", []any{vt, map[string]any{"kind": "bool"}},
					map[string]any{"stmt": "map-lookup", "base": base, "index": idx, "keyType": kt, "valueType": vt}, false)
				valTys = []types.Type{mt.Elem(), types.Typ[types.Bool]}
			}
		case *ast.TypeAssertExpr:
			if r.Type != nil {
				operand, err := b.value(r.X)
				if err != nil {
					return nil, err
				}
				target, err := e.emitType(e.goTypeOf(r.Type))
				if err != nil {
					return nil, err
				}
				vals = b.wideOcc("assert", []any{target, map[string]any{"kind": "bool"}},
					map[string]any{"stmt": "type-assert", "operand": operand, "target": target}, false)
				valTys = []types.Type{e.goTypeOf(r.Type), types.Typ[types.Bool]}
			}
		}
	}
	if vals == nil && len(st.Rhs) == 1 {
		call, isCall := ast.Unparen(st.Rhs[0]).(*ast.CallExpr)
		if !isCall {
			return nil, unsup("unseq lowering: multi-target assignment with a single non-call right-hand side")
		}
		tup, isTup := e.goTypeOf(call).(*types.Tuple)
		if !isTup || tup.Len() != len(st.Lhs) {
			return nil, unsup("unseq lowering: multi-value call arity")
		}
		slots, err := b.call(call, len(st.Lhs))
		if err != nil {
			return nil, err
		}
		vals = slots
		for i := 0; i < tup.Len(); i++ {
			valTys = append(valTys, tup.At(i).Type())
		}
	}
	if vals == nil {
		if len(st.Lhs) != len(st.Rhs) {
			return nil, unsup("unseq lowering: assignment arity")
		}
		for _, r := range st.Rhs {
			w, err := b.value(r)
			if err != nil {
				return nil, err
			}
			vals = append(vals, w)
			valTys = append(valTys, e.goTypeOf(r))
		}
	}
	if len(vals) != len(st.Lhs) {
		return nil, unsup("unseq lowering: %d values for %d targets", len(vals), len(st.Lhs))
	}
	anyPlanned := false
	for _, l := range st.Lhs {
		if b.isPlannedTarget(l) {
			anyPlanned = true
		}
	}
	if anyPlanned {
		// phase 2 through the store list: every non-blank target a plan, in order
		for i, l := range st.Lhs {
			if isBlankTarget(l) {
				continue
			}
			var t string
			if p, isPrepared := prepared[i]; isPrepared {
				var err error
				t, err = b.emitPrepared(p)
				if err != nil {
					return nil, err
				}
			} else {
				id, isIdent := ast.Unparen(l).(*ast.Ident)
				if !isIdent {
					return nil, unsup("unseq lowering: multi-target plain target %T", l)
				}
				t = b.varTarget(id)
			}
			ty, err := e.typeOf(l)
			if err != nil {
				return nil, err
			}
			cell, _ := b.ensureCell(vals[i], ty)
			b.stores = append(b.stores, map[string]any{"target": t, "value": cell})
		}
		return emptyBlock(), nil
	}
	lhs := []any{}
	rhs := []any{}
	for i, l := range st.Lhs {
		w, err := e.emitAssignTargetPhase1(l, define)
		if err != nil {
			return nil, err
		}
		lhs = append(lhs, w)
		v := vals[i]
		if !isBlankTarget(l) {
			v, err = e.wrapInterfaceConversion(e.assignTargetType(l, define), valTys[i], v)
			if err != nil {
				return nil, err
			}
		}
		rhs = append(rhs, v)
	}
	return map[string]any{"stmt": "assign", "define": define, "lhs": lhs, "rhs": rhs}, nil
}

// allocOcc emits an `allocate` occurrence binding a fresh cell of type ty: a
// composite literal in the RESIDUAL (no E1 edge); `make`/`new` as an EVENT with
// the E1 anchor (the caller has pushed the operand frame, popped here).
func (b *unseqBuilder) allocOcc(kind string, ty any, spec map[string]any, event bool) any {
	cell := b.newCell(ty)
	name := b.occName(kind)
	o := map[string]any{"name": name, "kind": "allocate", "bind": cell, "allocation": spec}
	if !event {
		b.emit(o)
		return slotIdent(cell, ty)
	}
	if after := b.eventAfter(); after != nil {
		o["after"] = after
	}
	if b.region != "" {
		o["region"] = b.region
	}
	block := append(b.pop(), o)
	b.emitEventBlock(block)
	b.anchor = name
	return slotIdent(cell, ty)
}

// wideOcc emits a `wide` occurrence (Stage E5 E5a): a built-in the machine models
// as a wide statement, its results into fresh cells of the given types, as an
// E1-ordered EVENT with the anchor (the caller has pushed the operand frame,
// popped here). Returns the result slots.
func (b *unseqBuilder) wideOcc(kind string, tys []any, spec map[string]any, event bool) []any {
	binds := []any{}
	slots := []any{}
	for _, ty := range tys {
		cell := b.newCell(ty)
		binds = append(binds, cell)
		slots = append(slots, slotIdent(cell, ty))
	}
	name := b.occName(kind)
	o := map[string]any{"name": name, "kind": "wide", "binds": binds, "wide": spec}
	if !event {
		// E5b: the comma-ok lookup / assertion — a read / a pure op in the RESIDUAL (no E1 edge)
		b.emit(o)
		return slots
	}
	if after := b.eventAfter(); after != nil {
		o["after"] = after
	}
	if b.region != "" {
		o["region"] = b.region
	}
	block := append(b.pop(), o)
	b.emitEventBlock(block)
	b.anchor = name
	return slots
}

// bytesOperand lowers a slice operand, or a STRING operand as the pure
// `bytes-from-string` head over its atom (the legacy `byteSliceOrWrappedString`).
func (b *unseqBuilder) bytesOperand(x ast.Expr) (any, error) {
	w, err := b.value(x)
	if err != nil {
		return nil, err
	}
	if isStringType(types.Unalias(b.e.goTypeOf(x)).Underlying()) {
		bytesTy := map[string]any{"kind": "slice", "elem": intType("uint8")}
		return b.evalOcc("conv", bytesTy, map[string]any{"expr": "bytes-from-string", "x": w}), nil
	}
	return w, nil
}

// wideAppend lowers `append(s, x…)` / `append(s, t...)` (Stage E5 E5a) inside the
// call's operand frame: the base atom, the elements — a non-spread list packed
// into a slice literal (an `allocate` in the frame, no E1 edge — the legacy
// hoist's own packing), a spread slice as its atom, a spread string as a
// bytes-from-string head — then the `wide` append event.
func (b *unseqBuilder) wideAppend(c *ast.CallExpr) (any, error) {
	e := b.e
	resTy := e.goTypeOf(c)
	sl, ok := types.Unalias(resTy).Underlying().(*types.Slice)
	if !ok {
		return nil, unsup("unseq lowering: append result is not a slice")
	}
	elemTy, err := e.emitType(sl.Elem())
	if err != nil {
		return nil, err
	}
	base, err := b.value(c.Args[0])
	if err != nil {
		return nil, err
	}
	var elems any
	if c.Ellipsis != token.NoPos {
		elems, err = b.bytesOperand(c.Args[1])
		if err != nil {
			return nil, err
		}
	} else {
		packed := []any{}
		for i := 1; i < len(c.Args); i++ {
			w, err := b.value(c.Args[i])
			if err != nil {
				return nil, err
			}
			w, err = e.wrapInterfaceConversion(sl.Elem(), e.goTypeOf(c.Args[i]), w)
			if err != nil {
				return nil, err
			}
			packed = append(packed, map[string]any{"index": int64(i - 1), "value": w})
		}
		sliceTy := map[string]any{"kind": "slice", "elem": elemTy}
		elems = b.allocOcc("pack", sliceTy,
			map[string]any{"stmt": "slice-lit", "elem": elemTy, "length": int64(len(packed)), "elems": packed}, false)
	}
	ty, err := e.typeOf(c)
	if err != nil {
		return nil, err
	}
	return b.wideOcc("append", []any{ty},
		map[string]any{"stmt": "append", "elem": elemTy, "slice": base, "elems": elems}, true)[0], nil
}

// wideCopy lowers `copy(dst, src)` (Stage E5 E5a): the destination and source
// atoms (a string source as a bytes-from-string head), then the `wide` copy event
// producing the count.
func (b *unseqBuilder) wideCopy(c *ast.CallExpr) (any, error) {
	dst, err := b.value(c.Args[0])
	if err != nil {
		return nil, err
	}
	src, err := b.bytesOperand(c.Args[1])
	if err != nil {
		return nil, err
	}
	return b.wideOcc("copy", []any{intType("int")}, map[string]any{"stmt": "copy", "dst": dst, "src": src}, true)[0], nil
}

// recv lowers `<-ch` (Stage E E3): the channel value, then the RECEIVE as an
// E1-ordered event occurrence (kind "recv") writing its binder cell.
func (b *unseqBuilder) recv(u *ast.UnaryExpr) (any, error) {
	slots, _, err := b.recvN(u, 1)
	if err != nil {
		return nil, err
	}
	return slots[0], nil
}

// recvN lowers a receive with n binders (1: the value; 2 — Stage E5 E5b — the
// comma-ok pair, the second cell bool); returns the slots and the element type.
func (b *unseqBuilder) recvN(u *ast.UnaryExpr, n int) ([]any, types.Type, error) {
	e := b.e
	b.push()
	popped := false
	defer func() {
		if !popped {
			b.frames = b.frames[:len(b.frames)-1]
		}
	}()
	ch, err := b.value(u.X)
	if err != nil {
		return nil, nil, err
	}
	elemGo, err := e.chanElem(u.X)
	if err != nil {
		return nil, nil, err
	}
	elemTy, err := e.emitType(elemGo)
	if err != nil {
		return nil, nil, err
	}
	cell := b.newCell(elemTy)
	binds := []any{cell}
	slots := []any{slotIdent(cell, elemTy)}
	if n == 2 {
		boolTy := map[string]any{"kind": "bool"}
		ok := b.newCell(boolTy)
		binds = append(binds, ok)
		slots = append(slots, slotIdent(ok, boolTy))
	}
	name := b.occName("recv")
	o := map[string]any{"name": name, "kind": "recv", "binds": binds, "ch": ch, "elem": elemTy}
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
	return slots, elemGo, nil
}

// methodCallee lowers a concrete method call's callee (Stage E E3): the
// receiver argument (the sub-evaluation, inside the call's operand frame), the
// method's function key and its signature WITHOUT the receiver.
func (b *unseqBuilder) methodCallee(sel *ast.SelectorExpr) (any, string, *types.Signature, error) {
	e := b.e
	seln, ok := e.info.Selections[sel]
	if !ok || seln.Kind() != types.MethodVal {
		return nil, "", nil, unsup("unseq lowering: method callee without a selection")
	}
	fn, ok := seln.Obj().(*types.Func)
	if !ok {
		return nil, "", nil, unsup("unseq lowering: method callee without a function object")
	}
	msig := fn.Type().(*types.Signature)
	declRecv := msig.Recv().Type()
	pointerRecv := false
	if ptr, isPtr := types.Unalias(declRecv).Underlying().(*types.Pointer); isPtr {
		pointerRecv = true
		declRecv = ptr.Elem()
	}
	name, ok := e.namedTypeName(declRecv)
	if !ok {
		return nil, "", nil, unsup("unseq lowering: method on an anonymous receiver type")
	}
	member, err := declarationObjectName(fn)
	if err != nil {
		return nil, "", nil, err
	}
	recvT := e.goTypeOf(sel.X)
	opPtr, opIsPtr := types.Unalias(recvT).Underlying().(*types.Pointer)
	var recvArg any
	if pointerRecv {
		if opIsPtr {
			recvArg, err = b.value(sel.X)
			if err != nil {
				return nil, "", nil, err
			}
		} else if st, isStar := ast.Unparen(sel.X).(*ast.StarExpr); isStar {
			// (*p).M(): the nil-asserting address of the dereference (BUG-056/063)
			p, err := b.value(st.X)
			if err != nil {
				return nil, "", nil, err
			}
			pty, err := e.typeOf(st.X)
			if err != nil {
				return nil, "", nil, err
			}
			recvArg = b.evalOcc("recvaddr", pty, map[string]any{"expr": "addr-of-deref", "ptr": p})
		} else {
			// an addressable variable: its address, frozen (no read)
			id, isIdent := ast.Unparen(sel.X).(*ast.Ident)
			if !isIdent {
				return nil, "", nil, unsup("unseq lowering: pointer-receiver call on a non-variable operand")
			}
			recvArg, err = e.emitAddressOf(id)
			if err != nil {
				return nil, "", nil, err
			}
		}
	} else {
		v, err := b.value(sel.X)
		if err != nil {
			return nil, "", nil, err
		}
		if opIsPtr {
			elemTy, err := e.emitType(opPtr.Elem())
			if err != nil {
				return nil, "", nil, err
			}
			recvArg = b.evalOcc("recvderef", elemTy, map[string]any{"expr": "deref", "ptr": v, "type": elemTy})
		} else {
			recvArg = v
		}
	}
	sig, ok := seln.Type().(*types.Signature)
	if !ok {
		return nil, "", nil, unsup("unseq lowering: method callee without a call signature")
	}
	return recvArg, methodFuncKey(name, member), sig, nil
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

// fieldRecv lowers the receiver of a field read `x.f` (Stage E E2): through a
// pointer, `deref(ptr atom)` at the struct type; on a struct value, the base atom
// (an identifier — private or address-taken — is passed to `field-get` DIRECTLY,
// so the selection is one occurrence and no struct-typed cell is minted) or the
// slot a nested base produced. Returns the struct's wire name too.
func (b *unseqBuilder) fieldRecv(sel *ast.SelectorExpr) (any, string, error) {
	e := b.e
	bt := e.goTypeOf(sel.X)
	if ptr, isPtr := types.Unalias(bt).Underlying().(*types.Pointer); isPtr {
		p, err := b.value(sel.X)
		if err != nil {
			return nil, "", err
		}
		name, ok := e.namedTypeName(ptr.Elem())
		if !ok {
			return nil, "", unsup("unseq lowering: field selector on pointer to anonymous struct")
		}
		elemTy, err := e.emitType(ptr.Elem())
		if err != nil {
			return nil, "", err
		}
		return map[string]any{"expr": "deref", "ptr": p, "type": elemTy}, name, nil
	}
	name, ok := e.namedTypeName(bt)
	if !ok {
		return nil, "", unsup("unseq lowering: field selector on anonymous struct type %s", bt)
	}
	if id, isIdent := ast.Unparen(sel.X).(*ast.Ident); isIdent {
		w, err := e.emitIdent(id)
		if err != nil {
			return nil, "", err
		}
		m, isMap := w.(map[string]any)
		if !isMap || (m["expr"] != "ident" && m["expr"] != "deref") {
			return nil, "", unsup("unseq lowering: struct variable %s did not lower to an identifier or a global read (%v)", id.Name, w)
		}
		if m["expr"] == "deref" { // a package-level struct variable: field-get on the read value
			return m, name, nil
		}
		ty, err := e.typeOf(id)
		if err != nil {
			return nil, "", err
		}
		m["type"] = ty
		return m, name, nil
	}
	base, err := b.value(sel.X)
	if err != nil {
		return nil, "", err
	}
	return base, name, nil
}

// derefTarget lowers a dereference target plan `*p` on the FROZEN pointer value
// (Stage E E2) and returns its binder.
func (b *unseqBuilder) derefTarget(st *ast.StarExpr) (string, error) {
	ptr, err := b.value(st.X)
	if err != nil {
		return "", err
	}
	t := b.newTargetBinder()
	b.emit(map[string]any{"name": b.occName("target"), "kind": "target", "bind": t,
		"lhs": map[string]any{"target": "addr", "expr": ptr}})
	return t, nil
}

// fieldTarget lowers a field target plan `p.f` / `s.f` (Stage E E2): the anchor is
// the pointer VALUE (frozen atom) or the struct VARIABLE's address (`ref s` /
// `globaladdr` — a stable identity); the plan checks nothing.
func (b *unseqBuilder) fieldTarget(sel *ast.SelectorExpr) (string, error) {
	e := b.e
	bt := e.goTypeOf(sel.X)
	var base any
	var structT types.Type = bt
	if ptr, isPtr := types.Unalias(bt).Underlying().(*types.Pointer); isPtr {
		p, err := b.value(sel.X)
		if err != nil {
			return "", err
		}
		base, structT = p, ptr.Elem()
	} else {
		id, isIdent := ast.Unparen(sel.X).(*ast.Ident)
		if !isIdent {
			return "", unsup("unseq lowering: field target on a non-variable struct base")
		}
		addr, err := e.emitAddressOf(id)
		if err != nil {
			return "", err
		}
		base = addr
	}
	name, ok := e.namedTypeName(structT)
	if !ok {
		return "", unsup("unseq lowering: field target on anonymous struct type %s", structT)
	}
	t := b.newTargetBinder()
	b.emit(map[string]any{"name": b.occName("target"), "kind": "target", "bind": t,
		"lhs": map[string]any{"target": "addr", "expr": map[string]any{"expr": "field-addr", "base": base,
			"typeId": name, "field": sel.Sel.Name}}})
	return t, nil
}

// mapTarget lowers a map-element target plan `m[k]` on the FROZEN map value and
// key value (Stage E E2; `Assignee.mapElem`) and returns its binder.
func (b *unseqBuilder) mapTarget(ix *ast.IndexExpr, mt *types.Map) (string, error) {
	e := b.e
	base, err := b.value(ix.X)
	if err != nil {
		return "", err
	}
	key, err := b.value(ix.Index)
	if err != nil {
		return "", err
	}
	kt, err := e.emitType(mt.Key())
	if err != nil {
		return "", err
	}
	vt, err := e.emitType(mt.Elem())
	if err != nil {
		return "", err
	}
	t := b.newTargetBinder()
	b.emit(map[string]any{"name": b.occName("target"), "kind": "target", "bind": t,
		"lhs": map[string]any{"target": "map", "base": base, "index": key, "keyType": kt, "valueType": vt}})
	return t, nil
}

// isPlannedTarget: a slice element, a map element, a dereference or a FIELD (not a
// qualified package-level variable) — the targets lowered as FROZEN plans.
func (b *unseqBuilder) isPlannedTarget(lv ast.Expr) bool {
	switch l := ast.Unparen(lv).(type) {
	case *ast.IndexExpr, *ast.StarExpr:
		return true
	case *ast.SelectorExpr:
		_, isQual := b.e.unseqQualifiedPackageVar(l)
		return !isQual
	}
	return false
}

// preparedTarget is a planned target whose OPERANDS are lowered (E5b: in source
// order, before the right-hand values — spec#Order_of_evaluation orders the
// events lexically, and a call inside a target's index precedes the right-hand
// side's calls) but whose plan node is not yet emitted.
type preparedTarget struct {
	kind   string // "elem" | "map" | "deref" | "field"
	atoms  []any  // elem: base, index; map: base, key; deref: ptr; field: base (pointer atom or address)
	mt     *types.Map
	fieldT string // the struct's wire name (field)
	field  string
}

// prepareTarget lowers a planned target's operands (its events get their lexical
// E1 edges here) without emitting the plan.
func (b *unseqBuilder) prepareTarget(lv ast.Expr) (*preparedTarget, error) {
	e := b.e
	switch l := ast.Unparen(lv).(type) {
	case *ast.IndexExpr:
		base, err := b.value(l.X)
		if err != nil {
			return nil, err
		}
		idx, err := b.value(l.Index)
		if err != nil {
			return nil, err
		}
		if mt, isMap := types.Unalias(e.goTypeOf(l.X)).Underlying().(*types.Map); isMap {
			return &preparedTarget{kind: "map", atoms: []any{base, idx}, mt: mt}, nil
		}
		return &preparedTarget{kind: "elem", atoms: []any{base, idx}}, nil
	case *ast.StarExpr:
		ptr, err := b.value(l.X)
		if err != nil {
			return nil, err
		}
		return &preparedTarget{kind: "deref", atoms: []any{ptr}}, nil
	case *ast.SelectorExpr:
		bt := e.goTypeOf(l.X)
		var base any
		var structT types.Type = bt
		if ptr, isPtr := types.Unalias(bt).Underlying().(*types.Pointer); isPtr {
			p, err := b.value(l.X)
			if err != nil {
				return nil, err
			}
			base, structT = p, ptr.Elem()
		} else {
			id, isIdent := ast.Unparen(l.X).(*ast.Ident)
			if !isIdent {
				return nil, unsup("unseq lowering: field target on a non-variable struct base")
			}
			addr, err := e.emitAddressOf(id)
			if err != nil {
				return nil, err
			}
			base = addr
		}
		name, ok := e.namedTypeName(structT)
		if !ok {
			return nil, unsup("unseq lowering: field target on anonymous struct type %s", structT)
		}
		return &preparedTarget{kind: "field", atoms: []any{base}, fieldT: name, field: l.Sel.Name}, nil
	}
	return nil, unsup("unseq lowering: target plan %T outside the admitted grammar", lv)
}

// emitPrepared emits the plan node of a prepared target on its frozen atoms and
// returns its binder.
func (b *unseqBuilder) emitPrepared(p *preparedTarget) (string, error) {
	e := b.e
	t := b.newTargetBinder()
	var lhs map[string]any
	switch p.kind {
	case "elem":
		lhs = map[string]any{"target": "addr", "expr": map[string]any{"expr": "index-addr", "base": p.atoms[0], "index": p.atoms[1]}}
	case "map":
		kt, err := e.emitType(p.mt.Key())
		if err != nil {
			return "", err
		}
		vt, err := e.emitType(p.mt.Elem())
		if err != nil {
			return "", err
		}
		lhs = map[string]any{"target": "map", "base": p.atoms[0], "index": p.atoms[1], "keyType": kt, "valueType": vt}
	case "deref":
		lhs = map[string]any{"target": "addr", "expr": p.atoms[0]}
	case "field":
		lhs = map[string]any{"target": "addr", "expr": map[string]any{"expr": "field-addr", "base": p.atoms[0],
			"typeId": p.fieldT, "field": p.field}}
	default:
		return "", unsup("unseq lowering: prepared target kind %s", p.kind)
	}
	b.emit(map[string]any{"name": b.occName("target"), "kind": "target", "bind": t, "lhs": lhs})
	return t, nil
}

// planTarget lowers a planned target (isPlannedTarget) for an assignment /
// compound target `lv`, returning the binder and the target's element type wire.
func (b *unseqBuilder) planTarget(lv ast.Expr) (string, any, error) {
	e := b.e
	var t string
	var err error
	switch l := ast.Unparen(lv).(type) {
	case *ast.IndexExpr:
		if mt, isMap := types.Unalias(e.goTypeOf(l.X)).Underlying().(*types.Map); isMap {
			t, err = b.mapTarget(l, mt)
		} else {
			t, err = b.elemTarget(l)
		}
	case *ast.StarExpr:
		t, err = b.derefTarget(l)
	case *ast.SelectorExpr:
		t, err = b.fieldTarget(l)
	default:
		return "", nil, unsup("unseq lowering: target plan %T outside the admitted grammar", lv)
	}
	if err != nil {
		return "", nil, err
	}
	elemTy, err := e.typeOf(lv)
	if err != nil {
		return "", nil, err
	}
	return t, elemTy, nil
}

// plannedAssign lowers `lv = e` for a planned target: the plan, the value copied
// into a cell, the store in phase 2 (an empty completion).
func (b *unseqBuilder) plannedAssign(lv ast.Expr, rhs ast.Expr) (any, error) {
	t, elemTy, err := b.planTarget(lv)
	if err != nil {
		return nil, err
	}
	v, err := b.value(rhs)
	if err != nil {
		return nil, err
	}
	cell, _ := b.ensureCell(v, elemTy)
	b.stores = append(b.stores, map[string]any{"target": t, "value": cell})
	return emptyBlock(), nil
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
			if len(st.Lhs) != 1 || len(st.Rhs) != 1 {
				// Stage E5 E5b: the multi-target forms — every target a phase-1 sibling plan
				var err error
				then, err = b.multiAssign(st)
				if err != nil {
					return nil, err
				}
				break
			}
			if b.isPlannedTarget(st.Lhs[0]) {
				// a slice element, or (Stage E E2) a map element / a dereference / a
				// field: a FROZEN plan, the value copied into a cell, the store in phase 2
				var err error
				then, err = b.plannedAssign(st.Lhs[0], st.Rhs[0])
				if err != nil {
					return nil, err
				}
				break
			}
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

// readWrite lowers `lv op= rhs` (and `lv++`): a PLANNED target (a slice element;
// Stage E E2: a map element, a dereference, a field) — ONE frozen target plan
// shared by the load and the store: plan + load + op + store; a variable — a
// local (the read an occurrence when address-taken, the bare ident when
// private) or a package-level variable (Stage E E1; `g` or `pkg.V` — its READ
// occurrence, the store in `then` through the operand-free identity
// `addr(globaladdr)`) — the read + op, the store in `then`.
func (b *unseqBuilder) readWrite(lv ast.Expr, op string, rhs func() (any, error)) (any, error) {
	e := b.e
	if b.isPlannedTarget(lv) {
		t, elemTy, err := b.planTarget(lv)
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
	}
	switch l := ast.Unparen(lv).(type) {
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
