package main

// emit.go emits functions, statements, and expressions as wire nodes. Every
// expression node carries its resolved go/types type under "type" so the Lean
// lowering always has type information where GoCore needs it. Constructs not
// yet modeled return an unsupported error (fail closed).

import (
	"errors"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
)

// ---- program ----

func (e *emitter) emitProgram(files []*ast.File) (map[string]any, error) {
	funcs := []any{}
	methods := []any{}
	typeDefs := []any{}

	for _, f := range files {
		for _, decl := range f.Decls {
			switch d := decl.(type) {
			case *ast.FuncDecl:
				// main is the standalone entry point (it prints observations for
				// `go run`); GoCore runs the named subject, never main. Skip it,
				// matching the coverage harness.
				if d.Recv == nil && d.Name.Name == "main" {
					continue
				}
				// Lifted-literal names must be unique program-wide: methods
				// qualify by receiver type (A.go1$lit0 vs B.go1$lit0 — the
				// pre-merge audit found same-named methods colliding and the
				// wrong body executing). The decoder collision-checks too.
				e.curFuncName = d.Name.Name
				if d.Recv != nil && len(d.Recv.List) > 0 {
					rt := e.info.Defs[d.Name].Type().(*types.Signature).Recv().Type()
					if ptr, ok := rt.(*types.Pointer); ok {
						rt = ptr.Elem()
					}
					if rn, ok := namedTypeName(rt); ok {
						e.curFuncName = rn + "." + d.Name.Name
					}
				}
				e.liftSeq = 0
				fn, err := e.emitFuncDecl(d)
				if err != nil {
					// Per-decl quarantine: an UNSUPPORTED plain function
					// becomes a stub that fails closed when CALLED (params
					// typed unsupported carry the reason; arity preserved),
					// so one generic/float helper no longer poisons every
					// other subject in its file. Methods and non-unsupported
					// errors still fail the whole export.
					var u unsupported
					if errors.As(err, &u) && d.Recv == nil {
						e.lifted = nil
						arity := 0
						if d.Type.Params != nil {
							for _, f := range d.Type.Params.List {
								n := len(f.Names)
								if n == 0 {
									n = 1
								}
								arity += n
							}
						}
						funcs = append(funcs, map[string]any{
							"name": d.Name.Name, "unsupported": u.what, "arity": arity})
						continue
					}
					return nil, err
				}
				funcs = append(funcs, e.lifted...)
				e.lifted = nil
				if d.Recv != nil {
					methods = append(methods, fn)
				} else {
					funcs = append(funcs, fn)
				}
			case *ast.GenDecl:
				tds, err := e.emitGenDeclTypes(d)
				if err != nil {
					return nil, err
				}
				typeDefs = append(typeDefs, tds...)
			}
		}
	}

	return map[string]any{
		"schema":  "golean-native-v1",
		"package": e.pkg.Name(),
		"types":   typeDefs,
		"funcs":   funcs,
		"methods": methods,
	}, nil
}

// emitGenDeclTypes emits type declarations (only defined struct types carry a
// GoCore TypeDef today; defined types over primitives/maps/arrays are handled
// by their use-site types, and their methods by the method table).
func (e *emitter) emitGenDeclTypes(d *ast.GenDecl) ([]any, error) {
	if d.Tok != token.TYPE {
		return nil, nil
	}
	out := []any{}
	for _, spec := range d.Specs {
		ts := spec.(*ast.TypeSpec)
		obj := e.info.Defs[ts.Name]
		named, ok := obj.Type().(*types.Named)
		if !ok {
			continue
		}
		if st, isStruct := named.Underlying().(*types.Struct); isStruct {
			fields := []any{}
			for i := 0; i < st.NumFields(); i++ {
				fld := st.Field(i)
				fty, err := e.emitType(fld.Type())
				if err != nil {
					return nil, err
				}
				fields = append(fields, map[string]any{"name": fld.Name(), "type": fty})
			}
			out = append(out, map[string]any{
				"name": ts.Name.Name,
				"def":  map[string]any{"kind": "struct", "fields": fields},
			})
			continue
		}
		if _, isInterface := named.Underlying().(*types.Interface); isInterface {
			// Interface types carry no GoCore TypeDef; their shape is the
			// interface type at use sites and dispatch uses the method table.
			continue
		}
		// Other defined types (over primitives, maps, arrays, slices) become
		// aliases to their underlying type so GoCore can resolve defaults,
		// conversions, and equality.
		underlying, err := e.emitType(named.Underlying())
		if err != nil {
			return nil, err
		}
		out = append(out, map[string]any{
			"name": ts.Name.Name,
			"def":  map[string]any{"kind": "alias", "target": underlying},
		})
	}
	return out, nil
}

// ---- functions ----

func (e *emitter) emitFuncDecl(d *ast.FuncDecl) (map[string]any, error) {
	sig := e.info.Defs[d.Name].Type().(*types.Signature)

	params, err := e.emitParams(sig.Params())
	if err != nil {
		return nil, err
	}
	results, err := e.emitResults(sig.Results())
	if err != nil {
		return nil, err
	}

	fn := map[string]any{
		"name":    d.Name.Name,
		"params":  params,
		"results": results,
	}

	if d.Recv != nil {
		recv := sig.Recv()
		rty, err := e.emitType(recv.Type())
		if err != nil {
			return nil, err
		}
		defType := recv.Type()
		if ptr, ok := defType.(*types.Pointer); ok {
			defType = ptr.Elem()
		}
		name, ok := namedTypeName(defType)
		if !ok {
			return nil, unsup("method on anonymous type %s", defType)
		}
		fn["recv"] = map[string]any{"id": localName(recv), "type": rty}
		fn["recvType"] = name
	}

	if d.Body == nil {
		return nil, unsup("bodyless function %s", d.Name.Name)
	}
	body, err := e.emitBlock(d.Body)
	if err != nil {
		return nil, err
	}
	fn["body"] = body
	return fn, nil
}

func (e *emitter) emitParams(t *types.Tuple) ([]any, error) {
	out := []any{}
	for i := 0; i < t.Len(); i++ {
		v := t.At(i)
		ty, err := e.emitType(v.Type())
		if err != nil {
			return nil, err
		}
		out = append(out, map[string]any{"id": localName(v), "type": ty})
	}
	return out, nil
}

// emitResults names unnamed results with stable synthetic ids so GoCore (which
// reads named result locals at frame exit) has a binding to write into.
func (e *emitter) emitResults(t *types.Tuple) ([]any, error) {
	out := []any{}
	for i := 0; i < t.Len(); i++ {
		v := t.At(i)
		ty, err := e.emitType(v.Type())
		if err != nil {
			return nil, err
		}
		id := localName(v)
		if id == "" || id == "_" {
			id = syntheticResult(i)
		}
		out = append(out, map[string]any{"id": id, "type": ty})
	}
	return out, nil
}

func syntheticResult(i int) string { return "$res" + itoa(i) }

// localName produces a stable identity for a variable. Source names are kept;
// GoCore's lexical scoping handles shadowing, so distinct same-named locals in
// different scopes are correctly distinguished at execution.
func localName(v *types.Var) string {
	if v == nil {
		return ""
	}
	return v.Name()
}

// ---- statements ----

func (e *emitter) emitBlock(b *ast.BlockStmt) (map[string]any, error) {
	body, err := e.emitStmtList(b.List)
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "block", "body": body}, nil
}

func (e *emitter) emitStmtList(list []ast.Stmt) ([]any, error) {
	out := []any{}
	for _, s := range list {
		// A-normal form: emit each statement with a fresh hoist accumulator, then
		// emit the hoisted temp bindings (from calls/allocs in its expressions)
		// immediately before it.
		saved := e.hoisted
		e.hoisted = nil
		w, err := e.emitStmt(s)
		hoists := e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, err
		}
		out = append(out, hoists...)
		out = append(out, w)
	}
	return out, nil
}

// hoist binds an effectful node (call/alloc) to a fresh temp before the current
// statement and returns a reference to that temp.
func (e *emitter) hoist(node any, resultType types.Type) (any, error) {
	if e.hoistForbidden != "" {
		return nil, unsup("call/allocation in %s (would change evaluation order)", e.hoistForbidden)
	}
	ty, err := e.emitType(resultType)
	if err != nil {
		return nil, err
	}
	name := "$c" + itoa(e.tmpSeq)
	e.tmpSeq++
	e.hoisted = append(e.hoisted, map[string]any{
		"stmt":   "assign",
		"define": true,
		"lhs":    []any{map[string]any{"target": "declare", "id": name, "type": ty}},
		"rhs":    []any{node},
	})
	return map[string]any{"expr": "ident", "name": name, "type": ty}, nil
}

// splatMultiCall hoists a multi-value call into per-result temps and returns
// the temp ident nodes — the lowering for tuple FORWARDING positions
// (`return f()`, `g(f())`, tuple-into-variadic): Go's one-unnamed-tuple
// forms become the same multi-target call statement the direct
// `a, b := f()` form already uses, so the decoder and machine see nothing
// new (W1, docs/2026-07-24_sequential-coverage-scoping.md).
func (e *emitter) splatMultiCall(c *ast.CallExpr) ([]any, error) {
	if e.hoistForbidden != "" {
		return nil, unsup("call/allocation in %s (would change evaluation order)", e.hoistForbidden)
	}
	tup, ok := e.info.TypeOf(c).(*types.Tuple)
	if !ok {
		return nil, unsup("multi-value splat of non-tuple call")
	}
	node, effectful, err := e.emitCallNode(c)
	if err != nil {
		return nil, err
	}
	if !effectful {
		return nil, unsup("multi-value splat of non-call")
	}
	lhs := []any{}
	idents := []any{}
	for i := 0; i < tup.Len(); i++ {
		ty, err := e.emitType(tup.At(i).Type())
		if err != nil {
			return nil, err
		}
		name := "$c" + itoa(e.tmpSeq)
		e.tmpSeq++
		lhs = append(lhs, map[string]any{"target": "declare", "id": name, "type": ty})
		idents = append(idents, map[string]any{"expr": "ident", "name": name, "type": ty})
	}
	e.hoisted = append(e.hoisted, map[string]any{
		"stmt":   "assign",
		"define": true,
		"lhs":    lhs,
		"rhs":    []any{node},
	})
	return idents, nil
}

func (e *emitter) emitStmt(s ast.Stmt) (any, error) {
	switch st := s.(type) {
	case *ast.BlockStmt:
		return e.emitBlock(st)
	case *ast.ReturnStmt:
		return e.emitReturn(st)
	case *ast.AssignStmt:
		return e.emitAssign(st)
	case *ast.DeclStmt:
		return e.emitDeclStmt(st)
	case *ast.IfStmt:
		return e.emitIf(st)
	case *ast.ForStmt:
		return e.emitFor(st)
	case *ast.RangeStmt:
		return e.emitRange(st)
	case *ast.IncDecStmt:
		return e.emitIncDec(st)
	case *ast.ExprStmt:
		// A call in statement position lowers directly to a GoCore call
		// statement (no value needed, so no hoist).
		if call, ok := st.X.(*ast.CallExpr); ok {
			if id, ok := call.Fun.(*ast.Ident); ok {
				if _, isBuiltin := e.info.Uses[id].(*types.Builtin); isBuiltin {
					switch id.Name {
					case "panic":
						return e.emitPanicStmt(call)
					case "delete":
						return e.emitDeleteStmt(call)
					case "clear":
						return e.emitClearStmt(call)
					}
				}
			}
			node, _, err := e.emitCallNode(call)
			if err != nil {
				return nil, err
			}
			return map[string]any{"stmt": "expr", "expr": node}, nil
		}
		expr, err := e.emitExpr(st.X)
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "expr", "expr": expr}, nil
	case *ast.SwitchStmt:
		return e.emitSwitch(st)
	case *ast.DeferStmt:
		// `defer f(args)`: the callee and arguments are evaluated NOW; the
		// pending call is prepended to the frame's chain and runs at frame
		// exit (W3 §9). A method value or closure callee is just an
		// expression, so this reuses the func-value machinery.
		if id, ok := st.Call.Fun.(*ast.Ident); ok {
			if _, isBuiltin := e.info.Uses[id].(*types.Builtin); isBuiltin {
				// `defer recover()` does NOT recover: recover must be called
				// BY a deferred function, not AS one (oracle-pinned by
				// panic-recover/defer-recover-builtin, arc doc §A3). It is a
				// semantic no-op, lowered to a deferred empty function so the
				// drain still observes a registration. Other deferred
				// builtins (incl. panic) fail closed.
				if id.Name == "recover" && len(st.Call.Args) == 0 {
					return e.emitDeferNoop(), nil
				}
				return nil, unsup("defer of builtin %s", id.Name)
			}
		}
		callee, err := e.emitExpr(st.Call.Fun)
		if err != nil {
			return nil, err
		}
		var dsig *types.Signature
		if tv, ok := e.info.Types[st.Call.Fun]; ok {
			dsig, _ = tv.Type.Underlying().(*types.Signature)
		}
		args, err := e.emitCallArgs(dsig, st.Call)
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "defer", "callee": callee, "args": args}, nil
	case *ast.BranchStmt:
		switch st.Tok {
		case token.BREAK:
			if st.Label != nil {
				return nil, unsup("labeled break")
			}
			return map[string]any{"stmt": "break"}, nil
		case token.CONTINUE:
			if st.Label != nil {
				return nil, unsup("labeled continue")
			}
			return map[string]any{"stmt": "continue"}, nil
		default:
			return nil, unsup("branch statement %s", st.Tok)
		}
	case *ast.EmptyStmt:
		return map[string]any{"stmt": "block", "body": []any{}}, nil
	default:
		return nil, unsup("statement %T at %s", s, e.fset.Position(s.Pos()))
	}
}

func (e *emitter) emitReturn(st *ast.ReturnStmt) (any, error) {
	// `return f()` forwarding a multi-value call: splat into temps and
	// return the temps (the hoisted call statement is spliced before the
	// return by the A-normal-form machinery).
	if len(st.Results) == 1 {
		if call, ok := st.Results[0].(*ast.CallExpr); ok {
			if _, isTup := e.info.TypeOf(call).(*types.Tuple); isTup {
				idents, err := e.splatMultiCall(call)
				if err != nil {
					return nil, err
				}
				return map[string]any{"stmt": "return", "results": idents}, nil
			}
		}
	}
	results := []any{}
	for _, r := range st.Results {
		w, err := e.emitExpr(r)
		if err != nil {
			return nil, err
		}
		results = append(results, w)
	}
	return map[string]any{"stmt": "return", "results": results}, nil
}

// containsIdent reports whether the expression mentions any of the given
// names as an identifier — the shadow-capture test for defines: in
// `x := x + 1` the RHS's x is the OUTER x (Go evaluates define RHSes
// before the new names exist), but the wire format carries names only, so
// the decoder's initialization-then-assign lowering would resolve it to
// the freshly-declared cell. Capturing defines pre-bind their RHSes to
// hoisted temps (evaluated before the statement, in the outer scope).
// Found via the W2 switch-init-shadow guardrail (2026-07-24): a latent
// general define bug, not a switch bug.
func (e *emitter) containsVarUse(x ast.Expr, names map[string]bool) bool {
	found := false
	ast.Inspect(x, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok && names[id.Name] {
			// Only VARIABLE uses shadow-capture: struct-literal field keys
			// and selector fields are idents too, but go/types resolves
			// them to field objects (found via returns/multi-result-method,
			// where the literal keys a:/b: matched the define targets).
			if v, ok := e.info.Uses[id].(*types.Var); ok && !v.IsField() {
				found = true
			}
		}
		return !found
	})
	return found
}

// implicitInterfaceConversionGuard fails closed when a value of
// non-interface static type flows into an interface-typed slot: the
// lowering has no interface wrap at assignment/argument sites yet, so the
// raw representation makes typed-nil and cross-dynamic-type comparisons
// silently WRONG (interfaces/typed-nil-pointer-compare pinned it — Go 111,
// raw lowering 1). The wrap lands with the interfaces campaign
// (docs/2026-07-25_arc-sequence.md item 3); until then this construct is a
// visible boundary refusal. An untyped-nil RHS is exact as-is.
func (e *emitter) implicitInterfaceConversionGuard(target types.Type, rhs types.Type) error {
	if target == nil || !types.IsInterface(target) {
		return nil
	}
	if rhs == nil {
		return nil
	}
	if b, ok := rhs.(*types.Basic); ok && b.Kind() == types.UntypedNil {
		return nil
	}
	if !types.IsInterface(rhs) {
		return unsup("implicit interface conversion (interfaces campaign)")
	}
	return nil
}

// assignTargetType resolves the static type of an assignment target for the
// guard above (a fresh `:=` definition's type comes from Defs; blanks skip).
func (e *emitter) assignTargetType(l ast.Expr, define bool) types.Type {
	if id, ok := l.(*ast.Ident); ok {
		if id.Name == "_" {
			return nil
		}
		if define {
			if obj, isDef := e.info.Defs[id]; isDef && obj != nil {
				return obj.Type()
			}
		}
	}
	return e.info.TypeOf(l)
}

func (e *emitter) emitAssign(st *ast.AssignStmt) (any, error) {
	define := st.Tok == token.DEFINE
	if !define && st.Tok != token.ASSIGN {
		// Compound assignment (+=, -=, ...) desugars to op then assign in Lean;
		// carry the operator through.
		op, ok := compoundOp(st.Tok)
		if !ok {
			return nil, unsup("assignment operator %s", st.Tok)
		}
		if len(st.Lhs) != 1 || len(st.Rhs) != 1 {
			return nil, unsup("compound assignment arity")
		}
		// Map element compound assign `m[k] op= v`: maps are not
		// addressable, so this is a read-then-store (emitMapCompound).
		if ix, ok := st.Lhs[0].(*ast.IndexExpr); ok {
			if mt, ok := e.info.TypeOf(ix.X).Underlying().(*types.Map); ok {
				return e.emitMapCompound(ix, mt, op, st.Rhs[0])
			}
		}
		target, read, err := e.emitReadWriteTarget(st.Lhs[0])
		if err != nil {
			return nil, err
		}
		rhs, err := e.emitExpr(st.Rhs[0])
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "compound-assign", "op": op, "target": target, "read": read, "rhs": rhs}, nil
	}

	// Map element assignment `m[k] = v` is a map store, not an addressed
	// index (maps are not addressable).
	if !define && len(st.Lhs) == 1 && len(st.Rhs) == 1 {
		if ix, ok := st.Lhs[0].(*ast.IndexExpr); ok {
			if m, ok := e.info.TypeOf(ix.X).Underlying().(*types.Map); ok {
				base, err := e.emitExpr(ix.X)
				if err != nil {
					return nil, err
				}
				index, err := e.emitExpr(ix.Index)
				if err != nil {
					return nil, err
				}
				value, err := e.emitExpr(st.Rhs[0])
				if err != nil {
					return nil, err
				}
				keyTy, err := e.emitType(m.Key())
				if err != nil {
					return nil, err
				}
				valTy, err := e.emitType(m.Elem())
				if err != nil {
					return nil, err
				}
				return map[string]any{"stmt": "map-assign", "base": base, "index": index, "value": value, "keyType": keyTy, "valueType": valTy}, nil
			}
		}
	}

	lhs := []any{}
	for _, l := range st.Lhs {
		w, err := e.emitAssignTarget(l, define)
		if err != nil {
			return nil, err
		}
		lhs = append(lhs, w)
	}
	// Interface-typed targets: fail closed on implicit conversion (both the
	// per-pair and the multi-value-call shapes).
	if len(st.Rhs) == len(st.Lhs) {
		for i, l := range st.Lhs {
			if err := e.implicitInterfaceConversionGuard(
				e.assignTargetType(l, define), e.info.TypeOf(st.Rhs[i])); err != nil {
				return nil, err
			}
		}
	} else if len(st.Rhs) == 1 {
		if tup, ok := e.info.TypeOf(st.Rhs[0]).(*types.Tuple); ok && tup.Len() == len(st.Lhs) {
			for i, l := range st.Lhs {
				if err := e.implicitInterfaceConversionGuard(
					e.assignTargetType(l, define), tup.At(i).Type()); err != nil {
					return nil, err
				}
			}
		}
	}
	// Shadow capture (see containsIdent): does any RHS mention a name this
	// define introduces?
	var defineNames map[string]bool
	captures := false
	if define {
		defineNames = map[string]bool{}
		for _, l := range st.Lhs {
			if id, ok := l.(*ast.Ident); ok && id.Name != "_" {
				if obj, isDef := e.info.Defs[id]; isDef && obj != nil {
					defineNames[id.Name] = true
				}
			}
		}
		for _, r := range st.Rhs {
			if e.containsVarUse(r, defineNames) {
				captures = true
			}
		}
	}
	// A single call on the RHS (possibly multi-value) is emitted un-hoisted so
	// the lowering makes it a call statement writing all targets; hoisting would
	// force its result into one temp, which fails for a multi-value return.
	// ONLY for plain identifier targets: the call statement's machine
	// semantics evaluate target ADDRESSES first, but gc runs the call first
	// and reads a plain index/pointer operand at store time (pre-merge audit
	// 2026-07-25, probe-verified: a[i] = f() with f mutating i uses the NEW
	// i). A single addressed target falls through to the generic path,
	// whose A-normal-form hoist gives exactly gc's call-first order; a
	// MULTI-value call onto addressed targets cannot be hoisted and fails
	// closed rather than silently reordering.
	allIdentTargets := true
	for _, l := range st.Lhs {
		if _, ok := l.(*ast.Ident); !ok {
			allIdentTargets = false
		}
	}
	if len(st.Rhs) == 1 {
		if call, ok := st.Rhs[0].(*ast.CallExpr); ok {
			// Builtins never produce multi-value results and their emitters
			// may HOIST statements as a side effect — the speculative
			// emitCallNode below would run those effects twice when it
			// falls through (copy-edge/eval-order caught copy executing
			// twice). Route builtin RHSes through the generic single-emit
			// path.
			isBuiltinCall := false
			if id, ok := call.Fun.(*ast.Ident); ok {
				if _, isB := e.info.Uses[id].(*types.Builtin); isB {
					isBuiltinCall = true
				}
			}
			if !isBuiltinCall && captures {
				// `x := f(x)`-shaped: the call's arguments would read the
				// fresh cells. Fail closed until the arg-level pre-binding
				// lands.
				return nil, unsup("self-shadowing define with call RHS")
			}
			isMultiValue := false
			if tup, ok := e.info.TypeOf(call).(*types.Tuple); ok && tup.Len() > 1 {
				isMultiValue = true
			}
			// gc's observed order differs by arity (both oracle-pinned):
			// multi-value assignments evaluate target ADDRESSES first
			// (multi-assign/target-eval-before-call), so they keep the call
			// statement; a SINGLE-value call onto an addressed target runs
			// the call first (multi-assign/index-target-rhs-call-order), so
			// it falls through to the generic hoist path below.
			if !isBuiltinCall && (allIdentTargets || isMultiValue) {
				node, effectful, err := e.emitCallNode(call)
				if err != nil {
					return nil, err
				}
				if effectful {
					return map[string]any{"stmt": "assign", "define": define, "lhs": lhs, "rhs": []any{node}}, nil
				}
			}
		}
	}
	rhs := []any{}
	for _, r := range st.Rhs {
		w, err := e.emitExpr(r)
		if err != nil {
			return nil, err
		}
		// Capturing define: pre-bind EVERY RHS to a hoisted temp (uniformly,
		// preserving left-to-right evaluation), so the values are read in
		// the outer scope before the declarations take effect.
		if captures {
			w, err = e.hoist(w, e.info.TypeOf(r))
			if err != nil {
				return nil, err
			}
		}
		rhs = append(rhs, w)
	}
	return map[string]any{"stmt": "assign", "define": define, "lhs": lhs, "rhs": rhs}, nil
}

// emitAssignTarget emits an lvalue. On `:=`, a target ident that go/types
// records as a new definition is a declaration (carries its type).
func (e *emitter) emitAssignTarget(l ast.Expr, define bool) (any, error) {
	if pname, ok := e.capturedPtr(l); ok {
		return map[string]any{"target": "addr",
			"expr": map[string]any{"expr": "ident", "name": pname}}, nil
	}
	if id, ok := l.(*ast.Ident); ok {
		if id.Name == "_" {
			return map[string]any{"target": "blank"}, nil
		}
		if define {
			if obj, isDef := e.info.Defs[id]; isDef && obj != nil {
				ty, err := e.emitType(obj.Type())
				if err != nil {
					return nil, err
				}
				return map[string]any{"target": "declare", "id": id.Name, "type": ty}, nil
			}
		}
		return map[string]any{"target": "var", "id": id.Name}, nil
	}
	// Non-ident lvalue (field, index, deref): emit as an addressed location.
	return e.emitLValue(l)
}

func (e *emitter) emitDeclStmt(st *ast.DeclStmt) (any, error) {
	gd, ok := st.Decl.(*ast.GenDecl)
	if !ok || gd.Tok != token.VAR {
		return nil, unsup("declaration statement %s", declTok(st))
	}
	// Shadow capture, same rule as `:=` (see emitAssign): `var x = x + 1`
	// initializers evaluate in the OUTER scope, but the decoder's
	// initialization-then-assign lowering would resolve the name to the
	// fresh cell. Pre-bind capturing initializers to hoisted temps.
	// (Pre-merge audit 2026-07-25: the := fix did not cover var.)
	declNames := map[string]bool{}
	for _, spec := range gd.Specs {
		for _, name := range spec.(*ast.ValueSpec).Names {
			if name.Name != "_" {
				declNames[name.Name] = true
			}
		}
	}
	decls := []any{}
	for _, spec := range gd.Specs {
		vs := spec.(*ast.ValueSpec)
		for i, name := range vs.Names {
			obj := e.info.Defs[name]
			ty, err := e.emitType(obj.Type())
			if err != nil {
				return nil, err
			}
			d := map[string]any{"id": name.Name, "type": ty}
			if i < len(vs.Values) {
				if err := e.implicitInterfaceConversionGuard(
					obj.Type(), e.info.TypeOf(vs.Values[i])); err != nil {
					return nil, err
				}
				init, err := e.emitExpr(vs.Values[i])
				if err != nil {
					return nil, err
				}
				if e.containsVarUse(vs.Values[i], declNames) {
					init, err = e.hoist(init, e.info.TypeOf(vs.Values[i]))
					if err != nil {
						return nil, err
					}
				}
				d["init"] = init
			}
			decls = append(decls, d)
		}
	}
	return map[string]any{"stmt": "var", "decls": decls}, nil
}

func (e *emitter) emitIf(st *ast.IfStmt) (any, error) {
	node := map[string]any{"stmt": "if"}
	if st.Init != nil {
		init, err := e.emitStmt(st.Init)
		if err != nil {
			return nil, err
		}
		node["init"] = init
	}
	cond, err := e.emitExpr(st.Cond)
	if err != nil {
		return nil, err
	}
	node["cond"] = cond
	then, err := e.emitBlock(st.Body)
	if err != nil {
		return nil, err
	}
	node["then"] = then
	if st.Else != nil {
		// An `else if` condition is evaluated ONLY when the earlier tests
		// fail, so any call it hoists must land INSIDE the else branch. The
		// enclosing accumulator would place it before the whole chain, making
		// every later condition eager — pre-existing bug, unreachable until
		// closures let a case observe it (`if/else-if-first-match`).
		saved := e.hoisted
		e.hoisted = nil
		els, err := e.emitStmt(st.Else)
		elseHoists := e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, err
		}
		if len(elseHoists) > 0 {
			els = map[string]any{"stmt": "block",
				"body": append(append([]any{}, elseHoists...), els)}
		}
		node["else"] = els
	}
	return node, nil
}

func (e *emitter) emitFor(st *ast.ForStmt) (any, error) {
	// Go >= 1.22: each ForClause iteration has its OWN loop variable, so a
	// func literal in the body capturing it must see a per-iteration cell.
	// Our lowering declares the variable once outside the loop (one shared
	// cell) — a silent wrong answer for escaping captures (pre-merge audit
	// 2026-07-25; range loops are per-iteration already and are fine). Fail
	// closed until the per-iteration desugar lands. `defer f(i)` is fine —
	// args evaluate at defer time; only literal BODIES capture.
	if st.Init != nil {
		loopVars := map[types.Object]bool{}
		if as, ok := st.Init.(*ast.AssignStmt); ok && as.Tok == token.DEFINE {
			for _, l := range as.Lhs {
				if id, ok := l.(*ast.Ident); ok {
					if obj := e.info.Defs[id]; obj != nil {
						loopVars[obj] = true
					}
				}
			}
		}
		if len(loopVars) > 0 {
			captured := false
			ast.Inspect(st.Body, func(n ast.Node) bool {
				lit, ok := n.(*ast.FuncLit)
				if !ok {
					return true
				}
				ast.Inspect(lit, func(m ast.Node) bool {
					if id, ok := m.(*ast.Ident); ok {
						if obj := e.info.Uses[id]; obj != nil && loopVars[obj] {
							captured = true
						}
					}
					return !captured
				})
				return !captured
			})
			if captured {
				return nil, unsup("func literal captures a for-clause loop variable (Go 1.22 per-iteration semantics not yet lowered)")
			}
		}
	}
	node := map[string]any{"stmt": "for"}
	if st.Init != nil {
		init, err := e.emitStmt(st.Init)
		if err != nil {
			return nil, err
		}
		node["init"] = init
	}
	if st.Cond != nil {
		// The loop condition is re-evaluated each iteration; a hoist would move
		// it before the loop.
		cond, err := e.emitGuarded(true, "loop condition", st.Cond)
		if err != nil {
			return nil, err
		}
		node["cond"] = cond
	}
	if st.Post != nil {
		// The post statement runs every iteration; hoists from it must stay
		// inside it rather than escaping to before the loop (same class as
		// the else-if fix above).
		saved := e.hoisted
		e.hoisted = nil
		post, err := e.emitStmt(st.Post)
		postHoists := e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, err
		}
		if len(postHoists) > 0 {
			post = map[string]any{"stmt": "block",
				"body": append(append([]any{}, postHoists...), post)}
		}
		node["post"] = post
	}
	body, err := e.emitBlock(st.Body)
	if err != nil {
		return nil, err
	}
	node["body"] = body
	return node, nil
}

// rangeVarName returns the loop-variable name, or "" for absent/blank (`_`).
func rangeVarName(x ast.Expr) string {
	id, ok := x.(*ast.Ident)
	if !ok || id.Name == "_" {
		return ""
	}
	return id.Name
}

func nameOrNull(s string) any {
	if s == "" {
		return nil
	}
	return s
}

// emitRange emits `for k, v := range X`. Map range becomes the GoCore mapRange
// primitive; index-able ranges (slice/array/int) carry a "kind" that NativeToIR
// desugars to an index for-loop. Only `:=` range vars are modeled for now.
func (e *emitter) emitRange(rs *ast.RangeStmt) (any, error) {
	if rs.Key != nil && rs.Tok == token.ASSIGN {
		return nil, unsup("range with assigned (non-:=) variables")
	}
	coll, err := e.emitExpr(rs.X)
	if err != nil {
		return nil, err
	}
	body, err := e.emitBlock(rs.Body)
	if err != nil {
		return nil, err
	}
	node := map[string]any{
		"stmt":       "range",
		"keyVar":     nameOrNull(rangeVarName(rs.Key)),
		"valVar":     nameOrNull(rangeVarName(rs.Value)),
		"collection": coll,
		"body":       body,
	}
	switch u := e.info.TypeOf(rs.X).Underlying().(type) {
	case *types.Map:
		kt, err := e.emitType(u.Key())
		if err != nil {
			return nil, err
		}
		vt, err := e.emitType(u.Elem())
		if err != nil {
			return nil, err
		}
		node["kind"] = "map"
		node["keyType"] = kt
		node["valueType"] = vt
	case *types.Slice:
		et, err := e.emitType(u.Elem())
		if err != nil {
			return nil, err
		}
		node["kind"] = "slice"
		node["elemType"] = et
	case *types.Array:
		et, err := e.emitType(u.Elem())
		if err != nil {
			return nil, err
		}
		node["kind"] = "array"
		node["elemType"] = et
	case *types.Basic:
		if u.Info()&types.IsInteger != 0 {
			node["kind"] = "int"
		} else {
			return nil, unsup("range over %s", u)
		}
	default:
		return nil, unsup("range over %s", e.info.TypeOf(rs.X))
	}
	return node, nil
}

// emitReadWriteTarget emits the (target, read) pair for a read-modify-write
// statement (compound assign, ++/--). Go evaluates the operand's ADDRESS
// once; emitting target and read independently would run any call in the
// lvalue twice (`structs/selector-eval-once`: get().x += 4 must call get
// once). When the lvalue is effectful, pre-bind its address to a temp and
// read through it; a pure lvalue keeps the direct two-emission form, whose
// double evaluation is unobservable.
func (e *emitter) emitReadWriteTarget(lv ast.Expr) (any, any, error) {
	if !containsCall(lv) {
		target, err := e.emitLValue(lv)
		if err != nil {
			return nil, nil, err
		}
		read, err := e.emitExpr(lv)
		if err != nil {
			return nil, nil, err
		}
		return target, read, nil
	}
	addr, err := e.emitAddressOf(lv)
	if err != nil {
		return nil, nil, err
	}
	lvTy, err := e.emitType(e.info.TypeOf(lv))
	if err != nil {
		return nil, nil, err
	}
	ref, err := e.hoist(addr, types.NewPointer(e.info.TypeOf(lv)))
	if err != nil {
		return nil, nil, err
	}
	target := map[string]any{"target": "addr", "expr": ref}
	read := map[string]any{"expr": "deref", "ptr": ref, "type": lvTy}
	return target, read, nil
}

// emitMapCompound lowers a map-element read-modify-write (`m[k] op= v`,
// `m[k]++`): base and key evaluated ONCE each into hoisted temps, read via
// map-get, store via map-assign.
// rhsExpr may be nil (IncDec), in which case a literal 1 is used. The RHS is
// emitted AFTER base and key so its effects come last (gc's order — the
// first refactor emitted it first and maps/compound-assign-eval-once
// caught the swap immediately).
func (e *emitter) emitMapCompound(ix *ast.IndexExpr, mt *types.Map, op string, rhsExpr ast.Expr) (any, error) {
	baseW, err := e.emitExpr(ix.X)
	if err != nil {
		return nil, err
	}
	baseRef, err := e.hoist(baseW, e.info.TypeOf(ix.X))
	if err != nil {
		return nil, err
	}
	keyW, err := e.emitExpr(ix.Index)
	if err != nil {
		return nil, err
	}
	keyRef, err := e.hoist(keyW, mt.Key())
	if err != nil {
		return nil, err
	}
	keyTy, err := e.emitType(mt.Key())
	if err != nil {
		return nil, err
	}
	valTy, err := e.emitType(mt.Elem())
	if err != nil {
		return nil, err
	}
	var rhs any = map[string]any{"expr": "int", "value": "1",
		"type": map[string]any{"kind": "int", "int": "int"}}
	if rhsExpr != nil {
		rhs, err = e.emitExpr(rhsExpr)
		if err != nil {
			return nil, err
		}
	}
	read := map[string]any{"expr": "map-get", "base": baseRef,
		"index": keyRef, "keyType": keyTy, "valueType": valTy}
	return map[string]any{"stmt": "map-compound-assign", "op": op,
		"base": baseRef, "index": keyRef, "read": read, "rhs": rhs,
		"keyType": keyTy, "valueType": valTy}, nil
}

func (e *emitter) emitIncDec(st *ast.IncDecStmt) (any, error) {
	op := "+"
	if st.Tok == token.DEC {
		op = "-"
	}
	// m[k]++ is a map read-modify-write, not an addressed location (maps are
	// not addressable) — same desugar as m[k] op= 1 (pre-merge audit
	// 2026-07-25: the op= path existed, the IncDec path did not).
	if ix, ok := st.X.(*ast.IndexExpr); ok {
		if mt, ok := e.info.TypeOf(ix.X).Underlying().(*types.Map); ok {
			return e.emitMapCompound(ix, mt, op, nil)
		}
	}
	target, read, err := e.emitReadWriteTarget(st.X)
	if err != nil {
		return nil, err
	}
	// Carry the operand type so the synthetic 1 literal takes the operand's
	// integer kind (otherwise uint8-- would mix uint8 with an int literal).
	ty, err := e.typeOf(st.X)
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "incdec", "op": op, "target": target, "read": read, "type": ty}, nil
}

// ---- expressions ----

// emitSwitch (W2 slice 1, docs/2026-07-24_sequential-coverage-scoping.md):
// an expression switch desugars to a nested if-chain inside a fresh block —
// the init statement and the once-evaluated tag temp scope to the switch;
// one branch per case VALUE in source order (lazy case-expression
// evaluation, so a panicking case expression fires exactly when Go's
// would); bodies duplicated across a multi-value case's values; default
// spliced as the final else regardless of source position. Fail-closed
// residue for later slices: fallthrough (BranchStmt default arm), bare
// break targeting the switch (breakStack), calls in case expressions
// (lazy position — hoisting would evaluate them eagerly), type switches
// (interfaces lane).
func (e *emitter) emitSwitch(st *ast.SwitchStmt) (any, error) {
	body := []any{}
	if st.Init != nil {
		sub, err := e.emitStmtList([]ast.Stmt{st.Init})
		if err != nil {
			return nil, err
		}
		body = append(body, sub...)
	}
	var tagRef any
	var tagTy any
	if st.Tag != nil {
		saved := e.hoisted
		e.hoisted = nil
		tagExpr, err := e.emitExpr(st.Tag)
		hoists := e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, err
		}
		ty, err := e.typeOf(st.Tag)
		if err != nil {
			return nil, err
		}
		tagTy = ty
		name := "$sw" + itoa(e.tmpSeq)
		e.tmpSeq++
		body = append(body, hoists...)
		body = append(body, map[string]any{
			"stmt":   "assign",
			"define": true,
			"lhs":    []any{map[string]any{"target": "declare", "id": name, "type": ty}},
			"rhs":    []any{tagExpr},
		})
		tagRef = map[string]any{"expr": "ident", "name": name, "type": ty}
	}
	type swClause struct {
		conds       []any // nil for default
		stmts       []any
		fallsThru   bool
		declares    bool
		effective   any // filled in reverse, chaining fallthrough targets
	}
	clauses := []swClause{}
	for _, raw := range st.Body.List {
		cc, ok := raw.(*ast.CaseClause)
		if !ok {
			return nil, unsup("switch body statement %T", raw)
		}
		list := cc.Body
		fallsThru := false
		if n := len(list); n > 0 {
			if br, ok := list[n-1].(*ast.BranchStmt); ok && br.Tok == token.FALLTHROUGH {
				fallsThru = true
				list = list[:n-1]
			}
		}
		declares := false
		for _, s := range list {
			switch d := s.(type) {
			case *ast.DeclStmt:
				declares = true
			case *ast.AssignStmt:
				if d.Tok == token.DEFINE {
					declares = true
				}
			}
		}
		cbody, err := e.emitStmtList(list)
		if err != nil {
			return nil, err
		}
		cl := swClause{stmts: cbody, fallsThru: fallsThru, declares: declares}
		if cc.List != nil {
			conds := []any{}
			for _, ce := range cc.List {
				cw, err := e.emitGuarded(true, "switch case expression", ce)
				if err != nil {
					return nil, err
				}
				var cond any
				if st.Tag == nil {
					cond = cw
				} else {
					cond = map[string]any{"expr": "binary", "op": "==", "x": tagRef, "y": cw, "operandType": tagTy}
				}
				conds = append(conds, cond)
			}
			cl.conds = conds
		}
		clauses = append(clauses, cl)
	}
	// Effective bodies, built in reverse: `fallthrough` runs the NEXT
	// clause's body without testing its case expression, so the effective
	// body of a falling-through clause is its own statements followed by
	// the next clause's effective body. Fail closed when the
	// falling-through clause declares names: inlining the next clause's
	// body inside this clause's scope would let those declarations shadow
	// what Go resolves in the outer scope (Go's clause scopes are
	// siblings, not nested).
	for i := len(clauses) - 1; i >= 0; i-- {
		stmts := clauses[i].stmts
		if clauses[i].fallsThru {
			if i+1 >= len(clauses) {
				return nil, unsup("fallthrough in final switch clause")
			}
			if clauses[i].declares {
				return nil, unsup("fallthrough out of a clause that declares names")
			}
			stmts = append(append([]any{}, stmts...), clauses[i+1].effective)
		}
		clauses[i].effective = map[string]any{"stmt": "block", "body": stmts}
	}
	var defaultBody any
	chainClauses := []swClause{}
	for _, cl := range clauses {
		if cl.conds == nil {
			defaultBody = cl.effective
			continue
		}
		chainClauses = append(chainClauses, cl)
	}
	chain := defaultBody
	for i := len(chainClauses) - 1; i >= 0; i-- {
		for j := len(chainClauses[i].conds) - 1; j >= 0; j-- {
			node := map[string]any{"stmt": "if", "cond": chainClauses[i].conds[j], "then": chainClauses[i].effective}
			if chain != nil {
				node["else"] = chain
			}
			chain = node
		}
	}
	if chain != nil {
		body = append(body, chain)
	}
	// The switch is a BREAKABLE SCOPE (Go): a bare `break` in any clause
	// exits it, while `continue`/`return` unwind past to the enclosing
	// loop/frame. GoCore models this directly (Stmt.breakable) rather than
	// by a flag desugaring — see the constructor's docstring.
	return map[string]any{"stmt": "breakable",
		"body": map[string]any{"stmt": "block", "body": body}}, nil
}

func (e *emitter) emitExpr(x ast.Expr) (any, error) {
	node, err := e.emitExprBare(x)
	if err != nil {
		return nil, err
	}
	m, ok := node.(map[string]any)
	if ok {
		if _, has := m["type"]; !has {
			if ty, terr := e.typeOf(x); terr == nil {
				m["type"] = ty
			}
		}
	}
	return node, nil
}

func (e *emitter) emitExprBare(x ast.Expr) (any, error) {
	// Constant expressions are folded at compile time in Go: a constant
	// subexpression has no runtime evaluation (e.g. -7/3 never divides at
	// runtime). Emit the folded value. Idents are handled separately so named
	// constants still resolve, but untyped/typed constant arithmetic folds here.
	if _, isIdent := x.(*ast.Ident); !isIdent {
		if tv, ok := e.info.Types[x]; ok && tv.Value != nil {
			return e.emitConstValue(tv)
		}
	}
	switch ex := x.(type) {
	case *ast.ParenExpr:
		return e.emitExprBare(ex.X)
	case *ast.Ident:
		return e.emitIdent(ex)
	case *ast.BasicLit:
		return e.emitBasicLit(ex)
	case *ast.BinaryExpr:
		return e.emitBinary(ex)
	case *ast.UnaryExpr:
		return e.emitUnaryExpr(ex)
	case *ast.CallExpr:
		return e.emitCall(ex)
	case *ast.CompositeLit:
		return e.emitCompositeLit(ex)
	case *ast.SelectorExpr:
		return e.emitSelector(ex)
	case *ast.IndexExpr:
		return e.emitIndex(ex)
	case *ast.StarExpr:
		return e.emitStar(ex)
	case *ast.SliceExpr:
		return e.emitSliceExpr(ex)
	case *ast.FuncLit:
		return e.emitFuncLit(ex)
	default:
		return nil, unsup("expression %T at %s", x, e.fset.Position(x.Pos()))
	}
}

func (e *emitter) emitSliceExpr(se *ast.SliceExpr) (any, error) {
	// Array bases slice through their address; slice/string bases by value.
	var base any
	var err error
	if _, isArray := e.info.TypeOf(se.X).Underlying().(*types.Array); isArray {
		base, err = e.emitAddressOf(se.X)
	} else {
		base, err = e.emitExpr(se.X)
	}
	if err != nil {
		return nil, err
	}
	low := any(map[string]any{"expr": "int", "value": "0", "type": intType("int")})
	if se.Low != nil {
		if low, err = e.emitExpr(se.Low); err != nil {
			return nil, err
		}
	}
	var high any
	if se.High != nil {
		if high, err = e.emitExpr(se.High); err != nil {
			return nil, err
		}
	} else {
		// default high is len(base)
		operand, err := e.emitExpr(se.X)
		if err != nil {
			return nil, err
		}
		opTy, err := e.typeOf(se.X)
		if err != nil {
			return nil, err
		}
		high = map[string]any{"expr": "builtin-len", "operand": operand, "operandType": opTy}
	}
	node := map[string]any{"expr": "slice", "base": base, "low": low, "high": high}
	if se.Slice3 && se.Max != nil {
		m, err := e.emitExpr(se.Max)
		if err != nil {
			return nil, err
		}
		node["max"] = m
	}
	return node, nil
}

// namedTypeName returns the declared name of a (possibly pointer-wrapped) named
// type, for use as a GoCore struct TypeId.
func namedTypeName(t types.Type) (string, bool) {
	if named, ok := t.(*types.Named); ok {
		return named.Obj().Name(), true
	}
	return "", false
}

// fieldBase emits the struct value a field selector reads from, auto-dereferencing
// a pointer receiver (Go's x.f where x is *T), and returns the struct's TypeId.
// methodReceiverArg emits the receiver operand for a method call or method
// value. Go's rule: with a POINTER receiver, an already-pointer base is used
// AS IS and an addressable value base has its address taken; with a VALUE
// receiver the base is copied. Taking the address of an already-pointer base
// would build a double pointer, which shows up as a field access on an addr
// (`methods/pointer-method-value-read`).
func (e *emitter) methodReceiverArg(sel *ast.SelectorExpr, pointerRecv bool) (any, error) {
	if !pointerRecv {
		return e.emitExpr(sel.X)
	}
	if _, alreadyPtr := e.info.TypeOf(sel.X).Underlying().(*types.Pointer); alreadyPtr {
		return e.emitExpr(sel.X)
	}
	return e.emitAddressOf(sel.X)
}

func (e *emitter) fieldBase(sel *ast.SelectorExpr) (any, string, error) {
	recvType := e.info.TypeOf(sel.X)
	base, err := e.emitExpr(sel.X)
	if err != nil {
		return nil, "", err
	}
	if ptr, ok := recvType.Underlying().(*types.Pointer); ok {
		name, ok := namedTypeName(ptr.Elem())
		if !ok {
			return nil, "", unsup("field selector on pointer to anonymous struct")
		}
		elemTy, err := e.emitType(ptr.Elem())
		if err != nil {
			return nil, "", err
		}
		return map[string]any{"expr": "deref", "ptr": base, "type": elemTy}, name, nil
	}
	name, ok := namedTypeName(recvType)
	if !ok {
		return nil, "", unsup("field selector on anonymous struct type %s", recvType)
	}
	return base, name, nil
}

func (e *emitter) emitSelector(sel *ast.SelectorExpr) (any, error) {
	if seln, ok := e.info.Selections[sel]; ok && seln.Kind() != types.FieldVal {
		// A METHOD VALUE `x.M`: the same representation as a lifted closure
		// (§8) — the receiver is simply the first captured value, because
		// methods already lower to functions taking the receiver first. Go
		// evaluates the receiver AT METHOD-VALUE TIME: a value receiver is
		// copied then (pinned by defer/defer-method-receiver-eval), a pointer
		// receiver captures the address so later mutation is visible
		// (defer/defer-pointer-receiver-live).
		if seln.Kind() == types.MethodVal {
			fn, ok := seln.Obj().(*types.Func)
			if !ok {
				return nil, unsup("method %s is not a func", sel.Sel.Name)
			}
			recvType := fn.Type().(*types.Signature).Recv().Type()
			if _, isIface := recvType.Underlying().(*types.Interface); isIface {
				return nil, unsup("interface method value %s", sel.Sel.Name)
			}
			defType := recvType
			pointerRecv := false
			if ptr, ok := recvType.(*types.Pointer); ok {
				defType = ptr.Elem()
				pointerRecv = true
			}
			name, ok := namedTypeName(defType)
			if !ok {
				return nil, unsup("method on anonymous type %s", defType)
			}
			recvArg, err := e.methodReceiverArg(sel, pointerRecv)
			if err != nil {
				return nil, err
			}
			return map[string]any{"expr": "func-value",
				"func": name + "." + fn.Name(), "captured": []any{recvArg}}, nil
		}
		return nil, unsup("non-field selector %s (method/expr)", sel.Sel.Name)
	}
	base, structName, err := e.fieldBase(sel)
	if err != nil {
		return nil, err
	}
	return map[string]any{"expr": "field-get", "recv": base, "typeId": structName, "field": sel.Sel.Name}, nil
}

func (e *emitter) emitIndex(ix *ast.IndexExpr) (any, error) {
	baseType := e.info.TypeOf(ix.X).Underlying()
	base, err := e.emitExpr(ix.X)
	if err != nil {
		return nil, err
	}
	index, err := e.emitExpr(ix.Index)
	if err != nil {
		return nil, err
	}
	if m, ok := baseType.(*types.Map); ok {
		keyTy, err := e.emitType(m.Key())
		if err != nil {
			return nil, err
		}
		valTy, err := e.emitType(m.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"expr": "map-get", "base": base, "index": index, "keyType": keyTy, "valueType": valTy}, nil
	}
	return map[string]any{"expr": "index-get", "base": base, "index": index}, nil
}

func (e *emitter) emitStar(st *ast.StarExpr) (any, error) {
	ptr, err := e.emitExpr(st.X)
	if err != nil {
		return nil, err
	}
	pointee, err := e.emitType(e.info.TypeOf(st))
	if err != nil {
		return nil, err
	}
	return map[string]any{"expr": "deref", "ptr": ptr, "type": pointee}, nil
}

// emitAddressOf handles &x forms.
func (e *emitter) emitAddressOf(x ast.Expr) (any, error) {
	if pname, ok := e.capturedPtr(x); ok {
		return map[string]any{"expr": "ident", "name": pname}, nil
	}
	switch ex := x.(type) {
	case *ast.Ident:
		return map[string]any{"expr": "ref", "id": ex.Name}, nil
	case *ast.SelectorExpr:
		// Field ADDRESS: the machine's fieldAddr builds Loc.field on an
		// address operand (W4). A pointer base already IS the address (Go
		// auto-derefs p.n); an addressable value base recurses — so a.b.c
		// becomes fieldAddr(fieldAddr(ref a)). The old code passed the
		// base VALUE here, which is the root of the struct-field-write
		// backlog class (untriaged-count 2026-07-25 entry).
		bt := e.info.TypeOf(ex.X)
		var base any
		var err error
		var defType types.Type
		if ptr, ok := bt.Underlying().(*types.Pointer); ok {
			base, err = e.emitExpr(ex.X)
			defType = ptr.Elem()
		} else {
			base, err = e.emitAddressOf(ex.X)
			defType = bt
		}
		if err != nil {
			return nil, err
		}
		structName, ok := namedTypeName(defType)
		if !ok {
			return nil, unsup("field address on anonymous struct type %s", defType)
		}
		return map[string]any{"expr": "field-addr", "base": base, "typeId": structName, "field": ex.Sel.Name}, nil
	case *ast.IndexExpr:
		// Index ADDRESS: a slice value carries its own base location, so
		// the slice VALUE is the operand; an ARRAY base needs its address
		// (same W4 class as fields).
		var base any
		var err error
		if _, isArray := e.info.TypeOf(ex.X).Underlying().(*types.Array); isArray {
			base, err = e.emitAddressOf(ex.X)
		} else {
			base, err = e.emitExpr(ex.X)
		}
		if err != nil {
			return nil, err
		}
		index, err := e.emitExpr(ex.Index)
		if err != nil {
			return nil, err
		}
		return map[string]any{"expr": "index-addr", "base": base, "index": index}, nil
	case *ast.StarExpr:
		// &(*p) is p.
		return e.emitExpr(ex.X)
	case *ast.ParenExpr:
		return e.emitAddressOf(ex.X)
	case *ast.CompositeLit:
		// &T{...}: allocate the composite and take its address (A-normal form:
		// hoist a `new` statement binding a temp to the pointer).
		if e.hoistForbidden != "" {
			return nil, unsup("&composite in %s", e.hoistForbidden)
		}
		val, err := e.emitCompositeLit(ex)
		if err != nil {
			return nil, err
		}
		elemTy, err := e.emitType(e.info.TypeOf(ex))
		if err != nil {
			return nil, err
		}
		ptrTy := map[string]any{"kind": "pointer", "elem": elemTy}
		name := "$c" + itoa(e.tmpSeq)
		e.tmpSeq++
		e.hoisted = append(e.hoisted, map[string]any{
			"stmt":     "new",
			"target":   map[string]any{"target": "declare", "id": name, "type": ptrTy},
			"value":    val,
			"elemType": elemTy,
		})
		return map[string]any{"expr": "ident", "name": name, "type": ptrTy}, nil
	default:
		return nil, unsup("address-of %T", x)
	}
}

// emitLValue emits an assignment target for an arbitrary addressable
// expression: plain locals stay `var`, everything else becomes an addressed
// location (`&x` form) that GoCore assigns through.
func (e *emitter) emitLValue(x ast.Expr) (any, error) {
	if pname, ok := e.capturedPtr(x); ok {
		return map[string]any{"target": "addr",
			"expr": map[string]any{"expr": "ident", "name": pname}}, nil
	}
	if id, ok := x.(*ast.Ident); ok {
		if id.Name == "_" {
			return map[string]any{"target": "blank"}, nil
		}
		return map[string]any{"target": "var", "id": id.Name}, nil
	}
	addr, err := e.emitAddressOf(x)
	if err != nil {
		return nil, err
	}
	return map[string]any{"target": "addr", "expr": addr}, nil
}

func (e *emitter) emitCompositeLit(cl *ast.CompositeLit) (any, error) {
	t := e.info.TypeOf(cl)
	switch u := t.Underlying().(type) {
	case *types.Struct:
		return e.emitStructLit(cl, t, u)
	case *types.Array:
		return e.emitArrayLit(cl, u)
	case *types.Slice:
		return e.emitSliceLit(cl, u)
	case *types.Map:
		return e.emitMapLit(cl, u)
	default:
		return nil, unsup("composite literal of type %s", t)
	}
}

// containsCall reports whether an expression performs a call (and so has an
// observable evaluation MOMENT, not just a value).
func containsCall(x ast.Expr) bool {
	found := false
	ast.Inspect(x, func(n ast.Node) bool {
		if _, ok := n.(*ast.CallExpr); ok {
			found = true
		}
		return !found
	})
	return found
}

func (e *emitter) emitStructLit(cl *ast.CompositeLit, t types.Type, st *types.Struct) (any, error) {
	target, err := e.emitType(t)
	if err != nil {
		return nil, err
	}
	// Collect keyed values by field name, if the literal is keyed.
	keyed := map[string]ast.Expr{}
	positional := []ast.Expr{}
	for _, elt := range cl.Elts {
		if kv, ok := elt.(*ast.KeyValueExpr); ok {
			keyed[kv.Key.(*ast.Ident).Name] = kv.Value
		} else {
			positional = append(positional, elt)
		}
	}
	// Go evaluates a keyed literal's values in SOURCE order, but GoCore's
	// structLit takes them in DECLARATION order. When a value performs a
	// call, that reordering is observable (`structs/keyed-literal-eval-order`),
	// so pre-bind the effectful ones to temps in source order and use the
	// temps below. Pure values need no temp — their evaluation moment is
	// unobservable.
	preBound := map[string]any{}
	for _, elt := range cl.Elts {
		kv, ok := elt.(*ast.KeyValueExpr)
		if !ok || !containsCall(kv.Value) {
			continue
		}
		w, err := e.emitExpr(kv.Value)
		if err != nil {
			return nil, err
		}
		ref, err := e.hoist(w, e.info.TypeOf(kv.Value))
		if err != nil {
			return nil, err
		}
		preBound[kv.Key.(*ast.Ident).Name] = ref
	}
	args := []any{}
	// GoCore structLit takes positional args in declared field order; fill
	// keyed literals in order with zero-value defaults for omitted fields.
	for i := 0; i < st.NumFields(); i++ {
		fld := st.Field(i)
		if len(positional) > 0 {
			if i >= len(positional) {
				return nil, unsup("positional struct literal missing field %s", fld.Name())
			}
			w, err := e.emitExpr(positional[i])
			if err != nil {
				return nil, err
			}
			args = append(args, w)
			continue
		}
		if ref, ok := preBound[fld.Name()]; ok {
			args = append(args, ref)
		} else if v, ok := keyed[fld.Name()]; ok {
			w, err := e.emitExpr(v)
			if err != nil {
				return nil, err
			}
			args = append(args, w)
		} else {
			fty, err := e.emitType(fld.Type())
			if err != nil {
				return nil, err
			}
			args = append(args, map[string]any{"expr": "default", "type": fty})
		}
	}
	return map[string]any{"expr": "struct-lit", "target": target, "args": args}, nil
}

// hoistSliceLit hoists a slice allocation (makeSlice + per-index assign) bound
// to a temp and returns the temp reference.
func (e *emitter) hoistSliceLit(elems []any, elemTy any, length int64) (any, error) {
	if e.hoistForbidden != "" {
		return nil, unsup("slice literal in %s", e.hoistForbidden)
	}
	sliceTy := map[string]any{"kind": "slice", "elem": elemTy}
	name := "$c" + itoa(e.tmpSeq)
	e.tmpSeq++
	e.hoisted = append(e.hoisted, map[string]any{
		"stmt":   "slice-lit",
		"target": map[string]any{"target": "declare", "id": name, "type": sliceTy},
		"elem":   elemTy,
		"length": length,
		"elems":  elems,
	})
	return map[string]any{"expr": "ident", "name": name, "type": sliceTy}, nil
}

func (e *emitter) emitSliceLit(cl *ast.CompositeLit, s *types.Slice) (any, error) {
	elemTy, err := e.emitType(s.Elem())
	if err != nil {
		return nil, err
	}
	elems := []any{}
	idx := int64(0)
	length := int64(0)
	for _, elt := range cl.Elts {
		if kv, ok := elt.(*ast.KeyValueExpr); ok {
			tv, ok := e.info.Types[kv.Key]
			if !ok || tv.Value == nil {
				return nil, unsup("slice literal key is not constant")
			}
			idx, _ = constant.Int64Val(tv.Value)
			v, err := e.emitExpr(kv.Value)
			if err != nil {
				return nil, err
			}
			elems = append(elems, map[string]any{"index": idx, "value": v})
		} else {
			v, err := e.emitExpr(elt)
			if err != nil {
				return nil, err
			}
			elems = append(elems, map[string]any{"index": idx, "value": v})
		}
		if idx+1 > length {
			length = idx + 1
		}
		idx++
	}
	return e.hoistSliceLit(elems, elemTy, length)
}

// emitMapLit hoists a map literal (an allocation) into a makeMap + per-entry
// assignments bound to a temp, and returns the temp reference.
func (e *emitter) emitMapLit(cl *ast.CompositeLit, m *types.Map) (any, error) {
	if e.hoistForbidden != "" {
		return nil, unsup("map literal in %s", e.hoistForbidden)
	}
	keyTy, err := e.emitType(m.Key())
	if err != nil {
		return nil, err
	}
	valTy, err := e.emitType(m.Elem())
	if err != nil {
		return nil, err
	}
	mapTy, err := e.emitType(m)
	if err != nil {
		return nil, err
	}
	entries := []any{}
	for _, elt := range cl.Elts {
		kv, ok := elt.(*ast.KeyValueExpr)
		if !ok {
			return nil, unsup("map literal element is not key:value")
		}
		k, err := e.emitExpr(kv.Key)
		if err != nil {
			return nil, err
		}
		v, err := e.emitExpr(kv.Value)
		if err != nil {
			return nil, err
		}
		entries = append(entries, map[string]any{"key": k, "value": v})
	}
	name := "$c" + itoa(e.tmpSeq)
	e.tmpSeq++
	e.hoisted = append(e.hoisted, map[string]any{
		"stmt":      "map-lit",
		"target":    map[string]any{"target": "declare", "id": name, "type": mapTy},
		"keyType":   keyTy,
		"valueType": valTy,
		"entries":   entries,
	})
	return map[string]any{"expr": "ident", "name": name, "type": mapTy}, nil
}

func (e *emitter) emitArrayLit(cl *ast.CompositeLit, arr *types.Array) (any, error) {
	elem, err := e.emitType(arr.Elem())
	if err != nil {
		return nil, err
	}
	elems := []any{}
	idx := int64(0)
	for _, elt := range cl.Elts {
		if kv, ok := elt.(*ast.KeyValueExpr); ok {
			kv2, ok := e.info.Types[kv.Key]
			if !ok || kv2.Value == nil {
				return nil, unsup("array literal key is not constant")
			}
			k, _ := constant.Int64Val(kv2.Value)
			idx = k
			w, err := e.emitExpr(kv.Value)
			if err != nil {
				return nil, err
			}
			elems = append(elems, map[string]any{"index": idx, "value": w})
		} else {
			w, err := e.emitExpr(elt)
			if err != nil {
				return nil, err
			}
			elems = append(elems, map[string]any{"index": idx, "value": w})
		}
		idx++
	}
	return map[string]any{"expr": "array-lit", "length": arr.Len(), "elem": elem, "elems": elems}, nil
}

// freeCaptures returns the variables a func literal captures: identifiers it
// USES that were declared outside it (and are not package-level funcs, types
// or constants), in deterministic source order.
func (e *emitter) freeCaptures(lit *ast.FuncLit) []*types.Var {
	inner := map[types.Object]bool{}
	ast.Inspect(lit, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			if obj, isDef := e.info.Defs[id]; isDef && obj != nil {
				inner[obj] = true
			}
		}
		return true
	})
	seen := map[types.Object]bool{}
	out := []*types.Var{}
	ast.Inspect(lit, func(n ast.Node) bool {
		id, ok := n.(*ast.Ident)
		if !ok {
			return true
		}
		v, isVar := e.info.Uses[id].(*types.Var)
		if !isVar || inner[v] || seen[v] || v.IsField() {
			return true
		}
		// Package-level variables are not captures (globals are unsupported
		// today and would fail closed elsewhere).
		if v.Parent() == nil || v.Parent() == e.pkg.Scope() {
			return true
		}
		seen[v] = true
		out = append(out, v)
		return true
	})
	return out
}

// emitFuncLit lambda-lifts a func literal (§8): the body becomes a synthetic
// top-level function whose leading parameters are POINTERS to the captured
// variables, and the expression becomes a func value carrying their
// addresses. Two closures over one variable therefore receive the same
// address — Go's capture-by-reference, made explicit.
func (e *emitter) emitFuncLit(lit *ast.FuncLit) (any, error) {
	sig, ok := e.info.TypeOf(lit).(*types.Signature)
	if !ok {
		return nil, unsup("func literal without a signature")
	}
	captures := e.freeCaptures(lit)

	name := e.curFuncName + "$lit" + itoa(e.liftSeq)
	e.liftSeq++

	// Parameters: captured pointers first, then the literal's own.
	params := []any{}
	capturedArgs := []any{}
	newCapture := map[types.Object]string{}
	for k, v := range e.captureParam {
		newCapture[k] = v // a nested literal still reaches outer captures
	}
	for _, v := range captures {
		pname := v.Name() + "$cap"
		pty, err := e.emitType(v.Type())
		if err != nil {
			return nil, err
		}
		params = append(params, map[string]any{"id": pname,
			"type": map[string]any{"kind": "pointer", "elem": pty}})
		// The captured ADDRESS at the creation site — itself a deref-free
		// reference, or the outer pointer parameter when re-capturing.
		if outer, ok := e.captureParam[v]; ok {
			capturedArgs = append(capturedArgs,
				map[string]any{"expr": "ident", "name": outer})
		} else {
			capturedArgs = append(capturedArgs,
				map[string]any{"expr": "ref", "id": v.Name()})
		}
		newCapture[v] = pname
	}
	own, err := e.emitParams(sig.Params())
	if err != nil {
		return nil, err
	}
	params = append(params, own...)
	results, err := e.emitResults(sig.Results())
	if err != nil {
		return nil, err
	}

	// Emit the body with the capture map in force and a fresh hoist context.
	savedCapture, savedHoisted, savedName := e.captureParam, e.hoisted, e.curFuncName
	e.captureParam, e.hoisted = newCapture, nil
	body, berr := e.emitBlock(lit.Body)
	e.captureParam, e.hoisted, e.curFuncName = savedCapture, savedHoisted, savedName
	if berr != nil {
		return nil, berr
	}

	e.lifted = append(e.lifted, map[string]any{
		"name": name, "params": params, "results": results, "body": body,
	})
	return map[string]any{"expr": "func-value", "func": name,
		"captured": capturedArgs}, nil
}

// capturedPtr reports the pointer-parameter name for a captured variable when
// emitting a lifted body (§8), so WRITE positions reach the shared cell too:
// `x = v` becomes `*x$cap = v`, and `&x` becomes the pointer itself.
func (e *emitter) capturedPtr(x ast.Expr) (string, bool) {
	id, ok := x.(*ast.Ident)
	if !ok || e.captureParam == nil {
		return "", false
	}
	obj := e.info.Uses[id]
	if obj == nil {
		return "", false
	}
	pname, ok := e.captureParam[obj]
	return pname, ok
}

func (e *emitter) emitIdent(id *ast.Ident) (any, error) {
	switch id.Name {
	case "true":
		return map[string]any{"expr": "bool", "value": true}, nil
	case "false":
		return map[string]any{"expr": "bool", "value": false}, nil
	case "nil":
		return map[string]any{"expr": "nil"}, nil
	}
	// A constant identifier folds to its value.
	if tv, ok := e.info.Types[id]; ok && tv.Value != nil {
		return e.emitConstValue(tv)
	}
	// A declared function used as a VALUE (`f := someFunc`) is a func value
	// with no captures — the same representation lifted literals get (§8).
	// Callee positions never reach here (emitCallNode handles them), so this
	// is exactly the value-position case.
	if fn, ok := e.info.Uses[id].(*types.Func); ok {
		if _, isSig := fn.Type().(*types.Signature); isSig {
			return map[string]any{"expr": "func-value", "func": fn.Name(),
				"captured": []any{}}, nil
		}
	}
	// Inside a lifted body, a captured variable is reached through its
	// pointer parameter (§8): reading `x` is `*x$ptr`.
	if obj := e.info.Uses[id]; obj != nil {
		if pname, ok := e.captureParam[obj]; ok {
			ty, err := e.emitType(obj.Type())
			if err != nil {
				return nil, err
			}
			return map[string]any{"expr": "deref",
				"ptr":  map[string]any{"expr": "ident", "name": pname},
				"type": ty}, nil
		}
	}
	return map[string]any{"expr": "ident", "name": id.Name}, nil
}

func (e *emitter) emitBasicLit(lit *ast.BasicLit) (any, error) {
	tv := e.info.Types[lit]
	return e.emitConstValue(tv)
}

func (e *emitter) emitConstValue(tv types.TypeAndValue) (any, error) {
	switch tv.Value.Kind() {
	case constant.Int:
		node := map[string]any{"expr": "int", "value": tv.Value.ExactString()}
		// Attach the underlying integer kind so a literal typed as a defined
		// type (e.g. `1` in `counter(uint64) + 1`) gets the right width, not
		// the default int. Set here so the generic type wrapper does not
		// override it with the named type.
		if b, ok := tv.Type.Underlying().(*types.Basic); ok && b.Info()&types.IsInteger != 0 {
			ty, err := e.emitBasic(b)
			if err != nil {
				return nil, err
			}
			node["type"] = ty
		}
		return node, nil
	case constant.Bool:
		return map[string]any{"expr": "bool", "value": constant.BoolVal(tv.Value)}, nil
	case constant.String:
		// The VALUE (escapes decoded) travels as raw BYTES: a Go string may
		// be invalid UTF-8 ("\xff"), and encoding/json silently replaces
		// invalid sequences with U+FFFD — which corrupted literal bytes
		// (wrong-answers slice 0b; strings/string-escape-bytes pinned it).
		bytes := []byte(constant.StringVal(tv.Value))
		vals := make([]any, len(bytes))
		for i, b := range bytes {
			vals[i] = int(b)
		}
		return map[string]any{"expr": "string", "bytes": vals}, nil
	default:
		return nil, unsup("constant kind %s", tv.Value.Kind())
	}
}

func (e *emitter) emitBinary(b *ast.BinaryExpr) (any, error) {
	op, ok := binaryOp(b.Op)
	if !ok {
		return nil, unsup("binary operator %s", b.Op)
	}
	x, err := e.emitExpr(b.X)
	if err != nil {
		return nil, err
	}
	// The RHS of a short-circuit operator is only conditionally evaluated, so a
	// call there cannot be hoisted ahead of the operator.
	y, err := e.emitGuarded(op == "&&" || op == "||", "short-circuit operand", b.Y)
	if err != nil {
		return nil, err
	}
	node := map[string]any{"expr": "binary", "op": op, "x": x, "y": y}
	// Comparisons need the operand type in GoCore; carry it explicitly.
	if isComparison(op) {
		oty, err := e.typeOf(b.X)
		if err != nil {
			return nil, err
		}
		node["operandType"] = oty
	}
	return node, nil
}

func (e *emitter) emitUnary(u *ast.UnaryExpr) (any, error) {
	x, err := e.emitExpr(u.X)
	if err != nil {
		return nil, err
	}
	switch u.Op {
	case token.SUB:
		return map[string]any{"expr": "unary", "op": "-", "x": x}, nil
	case token.ADD:
		return x, nil
	case token.NOT:
		return map[string]any{"expr": "unary", "op": "!", "x": x}, nil
	case token.XOR:
		return map[string]any{"expr": "unary", "op": "^", "x": x}, nil
	default:
		return nil, unsup("unary operator %s", u.Op)
	}
}

// emitUnaryExpr dispatches unary operators, routing & to address-of.
func (e *emitter) emitUnaryExpr(u *ast.UnaryExpr) (any, error) {
	if u.Op == token.AND {
		return e.emitAddressOf(u.X)
	}
	return e.emitUnary(u)
}

// emitCall in expression position: conversions are pure and returned inline;
// calls are effectful and hoisted (A-normal form) to a temp.
func (e *emitter) emitCall(c *ast.CallExpr) (any, error) {
	node, effectful, err := e.emitCallNode(c)
	if err != nil {
		return nil, err
	}
	if !effectful {
		return node, nil
	}
	return e.hoist(node, e.info.TypeOf(c))
}

// emitCallNode builds the wire node for a call/conversion and reports whether
// it is effectful (a call/allocation that must be sequenced) or pure (a
// conversion).
func (e *emitter) emitCallNode(c *ast.CallExpr) (any, bool, error) {
	// A callee position that is a type is a conversion T(x).
	if tv, ok := e.info.Types[c.Fun]; ok && tv.IsType() {
		if len(c.Args) != 1 {
			return nil, false, unsup("conversion with %d arguments", len(c.Args))
		}
		arg, err := e.emitExpr(c.Args[0])
		if err != nil {
			return nil, false, err
		}
		// String/byte/rune conversions have dedicated machine operators —
		// the generic convert op covers only scalar conversions (slice 1,
		// arc wrong-answers-builtins; these were latent backlog reds).
		tt := e.info.TypeOf(c).Underlying()
		ot := e.info.TypeOf(c.Args[0]).Underlying()
		if isByteSlice(tt) && isStringType(ot) {
			return map[string]any{"expr": "bytes-from-string", "x": arg}, false, nil
		}
		if isStringType(tt) && isByteSlice(ot) {
			return map[string]any{"expr": "string-from-bytes", "x": arg}, false, nil
		}
		if isStringType(tt) {
			if b, ok := ot.(*types.Basic); ok && b.Info()&types.IsInteger != 0 {
				return map[string]any{"expr": "string-from-rune", "x": arg}, false, nil
			}
		}
		target, err := e.emitType(e.info.TypeOf(c))
		if err != nil {
			return nil, false, err
		}
		return map[string]any{"expr": "convert", "target": target, "x": arg}, false, nil
	}

	// Method call x.M(args): a call to the receiver-scoped FuncId
	// "DefiningType.M" with the receiver prepended as the first argument.
	if sel, ok := c.Fun.(*ast.SelectorExpr); ok {
		return e.emitMethodCall(c, sel)
	}

	// An immediately-invoked func literal `func(){...}(args)`: lift the
	// literal (the ordinary §8 machinery) and call through the value.
	if lit, ok := c.Fun.(*ast.FuncLit); ok {
		callee, err := e.emitFuncLit(lit)
		if err != nil {
			return nil, false, err
		}
		lsig, _ := e.info.TypeOf(lit).Underlying().(*types.Signature)
		args, err := e.emitCallArgs(lsig, c)
		if err != nil {
			return nil, false, err
		}
		resultTypes, err := e.emitResultTypes(lsig)
		if err != nil {
			return nil, false, err
		}
		return map[string]any{"expr": "call-value", "callee": callee,
			"args": args, "resultTypes": resultTypes}, true, nil
	}

	fnID, ok := c.Fun.(*ast.Ident)
	if !ok {
		return nil, false, unsup("call target %T", c.Fun)
	}
	var sig *types.Signature
	switch obj := e.info.Uses[fnID].(type) {
	case *types.Func:
		sig, _ = obj.Type().(*types.Signature)
	case *types.Builtin:
		return e.emitBuiltin(c, fnID.Name)
	case *types.Var:
		// A call through a func-typed VARIABLE (closure or func value): the
		// callee is an expression, not a name (§8).
		vsig, ok := obj.Type().Underlying().(*types.Signature)
		if !ok {
			return nil, false, unsup("call to non-function variable %s", fnID.Name)
		}
		callee, err := e.emitExpr(fnID)
		if err != nil {
			return nil, false, err
		}
		args, err := e.emitCallArgs(vsig, c)
		if err != nil {
			return nil, false, err
		}
		resultTypes, err := e.emitResultTypes(vsig)
		if err != nil {
			return nil, false, err
		}
		return map[string]any{"expr": "call-value", "callee": callee,
			"args": args, "resultTypes": resultTypes}, true, nil
	default:
		return nil, false, unsup("call to non-function %s", fnID.Name)
	}
	args, err := e.emitCallArgs(sig, c)
	if err != nil {
		return nil, false, err
	}
	resultTypes, err := e.emitResultTypes(sig)
	if err != nil {
		return nil, false, err
	}
	return map[string]any{"expr": "call", "func": fnID.Name, "args": args, "resultTypes": resultTypes}, true, nil
}

// emitResultTypes emits a function signature's result types (used to type
// discard temps for blank call-result targets).
func (e *emitter) emitResultTypes(sig *types.Signature) ([]any, error) {
	out := []any{}
	if sig == nil {
		return out, nil
	}
	r := sig.Results()
	for i := 0; i < r.Len(); i++ {
		t, err := e.emitType(r.At(i).Type())
		if err != nil {
			return nil, err
		}
		out = append(out, t)
	}
	return out, nil
}

// emitCallArgs emits call arguments, collecting the trailing arguments of a
// variadic call into a slice (unless the call already spreads with `...`).
func (e *emitter) emitCallArgs(sig *types.Signature, c *ast.CallExpr) ([]any, error) {
	// Tuple forwarding `g(f())`: splat the inner multi-value call into
	// temps, then treat the temp idents as the argument list (variadic
	// packing proceeds over them like any other arguments).
	if len(c.Args) == 1 {
		if inner, ok := c.Args[0].(*ast.CallExpr); ok {
			if _, isTup := e.info.TypeOf(inner).(*types.Tuple); isTup {
				idents, err := e.splatMultiCall(inner)
				if err != nil {
					return nil, err
				}
				if sig == nil || !sig.Variadic() || c.Ellipsis != token.NoPos {
					return idents, nil
				}
				fixed := sig.Params().Len() - 1
				args := append([]any{}, idents[:fixed]...)
				elemType := sig.Params().At(fixed).Type().(*types.Slice).Elem()
				elemTy, err := e.emitType(elemType)
				if err != nil {
					return nil, err
				}
				// Zero variadic values pack as a NIL slice (Go: xs == nil
				// inside the callee), not an allocated empty one.
				if len(idents) == fixed {
					return append(args, map[string]any{"expr": "nil",
						"type": map[string]any{"kind": "slice", "elem": elemTy}}), nil
				}
				elems := []any{}
				for i := fixed; i < len(idents); i++ {
					elems = append(elems, map[string]any{"index": int64(i - fixed), "value": idents[i]})
				}
				sliceRef, err := e.hoistSliceLit(elems, elemTy, int64(len(idents)-fixed))
				if err != nil {
					return nil, err
				}
				return append(args, sliceRef), nil
			}
		}
	}
	if sig == nil || !sig.Variadic() || c.Ellipsis != token.NoPos {
		// Interface-typed params: fail closed on implicit conversion (a
		// spread argument is exact — the slice type already matches).
		if sig != nil && c.Ellipsis == token.NoPos {
			params := sig.Params()
			for i, a := range c.Args {
				if i < params.Len() {
					if err := e.implicitInterfaceConversionGuard(
						params.At(i).Type(), e.info.TypeOf(a)); err != nil {
						return nil, err
					}
				}
			}
		}
		return e.emitArgs(c.Args)
	}
	fixed := sig.Params().Len() - 1
	args := []any{}
	for i := 0; i < fixed; i++ {
		if err := e.implicitInterfaceConversionGuard(
			sig.Params().At(i).Type(), e.info.TypeOf(c.Args[i])); err != nil {
			return nil, err
		}
		w, err := e.emitExpr(c.Args[i])
		if err != nil {
			return nil, err
		}
		args = append(args, w)
	}
	elemType := sig.Params().At(fixed).Type().(*types.Slice).Elem()
	elemTy, err := e.emitType(elemType)
	if err != nil {
		return nil, err
	}
	// Zero variadic values pack as a NIL slice (Go: xs == nil inside the
	// callee — variadic/no-args-vs-empty-spread pins the distinction from
	// an explicit empty spread), not an allocated empty one.
	if len(c.Args) == fixed {
		return append(args, map[string]any{"expr": "nil",
			"type": map[string]any{"kind": "slice", "elem": elemTy}}), nil
	}
	elems := []any{}
	for i := fixed; i < len(c.Args); i++ {
		if err := e.implicitInterfaceConversionGuard(
			elemType, e.info.TypeOf(c.Args[i])); err != nil {
			return nil, err
		}
		w, err := e.emitExpr(c.Args[i])
		if err != nil {
			return nil, err
		}
		elems = append(elems, map[string]any{"index": int64(i - fixed), "value": w})
	}
	sliceRef, err := e.hoistSliceLit(elems, elemTy, int64(len(c.Args)-fixed))
	if err != nil {
		return nil, err
	}
	return append(args, sliceRef), nil
}

func (e *emitter) emitMethodCall(c *ast.CallExpr, sel *ast.SelectorExpr) (any, bool, error) {
	seln, ok := e.info.Selections[sel]
	if !ok || seln.Kind() != types.MethodVal {
		return nil, false, unsup("selector call %s is not a method value", sel.Sel.Name)
	}
	fn, ok := seln.Obj().(*types.Func)
	if !ok {
		return nil, false, unsup("method %s is not a func", sel.Sel.Name)
	}
	recvType := fn.Type().(*types.Signature).Recv().Type()
	// Interface-receiver methods need dynamic dispatch (interface increment).
	if _, isIface := recvType.Underlying().(*types.Interface); isIface {
		return nil, false, unsup("interface method dispatch %s", sel.Sel.Name)
	}
	// Defining type name (strip a pointer receiver) for the FuncId.
	defType := recvType
	pointerRecv := false
	if ptr, ok := recvType.(*types.Pointer); ok {
		defType = ptr.Elem()
		pointerRecv = true
	}
	name, ok := namedTypeName(defType)
	if !ok {
		return nil, false, unsup("method on anonymous type %s", defType)
	}
	// Receiver argument (see methodReceiverArg for Go's rule).
	recvArg, err := e.methodReceiverArg(sel, pointerRecv)
	if err != nil {
		return nil, false, err
	}
	args, err := e.emitCallArgs(fn.Type().(*types.Signature), c)
	if err != nil {
		return nil, false, err
	}
	all := append([]any{recvArg}, args...)
	resultTypes, err := e.emitResultTypes(fn.Type().(*types.Signature))
	if err != nil {
		return nil, false, err
	}
	return map[string]any{"expr": "call", "func": name + "." + sel.Sel.Name, "args": all, "resultTypes": resultTypes}, true, nil
}

// emitGuarded emits x, forbidding hoists while `guard` holds (restoring any
// prior guard afterward).
func (e *emitter) emitGuarded(guard bool, reason string, x ast.Expr) (any, error) {
	if !guard {
		return e.emitExpr(x)
	}
	saved := e.hoistForbidden
	e.hoistForbidden = reason
	w, err := e.emitExpr(x)
	e.hoistForbidden = saved
	return w, err
}

// emitBuiltin handles Go builtin calls. len/cap are pure expressions; the
// effectful builtins (make/append/...) are added incrementally.
func (e *emitter) emitBuiltin(c *ast.CallExpr, name string) (any, bool, error) {
	switch name {
	case "len", "cap":
		if len(c.Args) != 1 {
			return nil, false, unsup("%s with %d arguments", name, len(c.Args))
		}
		operand, err := e.emitExpr(c.Args[0])
		if err != nil {
			return nil, false, err
		}
		opTy, err := e.typeOf(c.Args[0])
		if err != nil {
			return nil, false, err
		}
		tag := "builtin-len"
		if name == "cap" {
			tag = "builtin-cap"
		}
		return map[string]any{"expr": tag, "operand": operand, "operandType": opTy}, false, nil
	case "make":
		return e.emitMake(c)
	case "new":
		// new(T): allocate T's zero value, yield the pointer (the same
		// hoisted "new" statement the &T{...} lowering uses, with a
		// default-value payload).
		if len(c.Args) != 1 {
			return nil, false, unsup("new with %d arguments", len(c.Args))
		}
		if e.hoistForbidden != "" {
			return nil, false, unsup("new in %s", e.hoistForbidden)
		}
		ptr, ok := e.info.TypeOf(c).(*types.Pointer)
		if !ok {
			return nil, false, unsup("new result is not a pointer")
		}
		elemTy, err := e.emitType(ptr.Elem())
		if err != nil {
			return nil, false, err
		}
		ptrTy := map[string]any{"kind": "pointer", "elem": elemTy}
		name := "$c" + itoa(e.tmpSeq)
		e.tmpSeq++
		e.hoisted = append(e.hoisted, map[string]any{
			"stmt":     "new",
			"target":   map[string]any{"target": "declare", "id": name, "type": ptrTy},
			"value":    map[string]any{"expr": "default", "type": elemTy},
			"elemType": elemTy,
		})
		return map[string]any{"expr": "ident", "name": name, "type": ptrTy}, false, nil
	case "append":
		return e.emitAppend(c)
	case "copy":
		return e.emitCopy(c)
	case "min", "max":
		// Pure strict operators over ints/strings; constant calls fold
		// before reaching here (go/types gives them a constant value, so
		// emitCallNode's conversion/constant paths never call us... but a
		// non-constant call lands here).
		if len(c.Args) == 0 {
			return nil, false, unsup("%s with no arguments", name)
		}
		args := []any{}
		for _, a := range c.Args {
			w, err := e.emitExpr(a)
			if err != nil {
				return nil, false, err
			}
			args = append(args, w)
		}
		return map[string]any{"expr": name, "args": args}, false, nil
	case "recover":
		if len(c.Args) != 0 {
			return nil, false, unsup("recover with %d arguments", len(c.Args))
		}
		// Effectful: recover marks the panic recovered, so it must keep its
		// source position in the evaluation order (the hoist machinery
		// sequences it like any call). The machine's continuation walk fires
		// wherever it actually evaluates.
		return map[string]any{"expr": "recover",
			"type": map[string]any{"kind": "interface", "name": "any"}}, true, nil
	case "panic":
		// panic(v) in a value position cannot type-check; reaching here means
		// an unmodeled context (e.g. panic as a call argument) — fail closed.
		return nil, false, unsup("builtin panic outside statement position")
	default:
		return nil, false, unsup("builtin %s", name)
	}
}

// emitPanicStmt lowers `panic(v)` to a wire panic statement. The payload is
// converted to `any` exactly as Go converts it: a non-interface argument
// carries its static type ("wrap") for the interface conversion; an argument
// already of interface type passes through bare; an untyped nil literal is a
// bare nil, which STAYS nil — the GOPATH-mode oracle keeps legacy panic(nil)
// semantics (recover() returns nil; the machine's panicPayload is the
// identity, arc doc §A2 correction).
func (e *emitter) emitPanicStmt(c *ast.CallExpr) (any, error) {
	if len(c.Args) != 1 {
		return nil, unsup("panic with %d arguments", len(c.Args))
	}
	arg := c.Args[0]
	t := e.info.TypeOf(arg)
	if b, ok := t.(*types.Basic); ok && b.Kind() == types.UntypedNil {
		return map[string]any{"stmt": "panic",
			"value": map[string]any{"expr": "nil"}}, nil
	}
	value, err := e.emitExpr(arg)
	if err != nil {
		return nil, err
	}
	if types.IsInterface(t) {
		return map[string]any{"stmt": "panic", "value": value}, nil
	}
	// A defined (named) non-struct type: the lowering models it as a GoCore
	// alias, so the interface wrap would erase its identity — and Go's abort
	// line prints it QUALIFIED (`main.T(v)`), which the bare value is not.
	// Fail closed (BUG-004). Named structs keep their identity (TypeId) and
	// pass through; their abort rendering fails closed machine-side.
	if named, ok := t.(*types.Named); ok {
		if _, isStruct := named.Underlying().(*types.Struct); !isStruct {
			return nil, unsup("panic payload of defined type %s (alias lowering erases its identity)", named.Obj().Name())
		}
	}
	wrap, err := e.emitType(t)
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "panic", "value": value, "wrap": wrap}, nil
}

// emitDeleteStmt lowers `delete(m, k)` (base evaluates before the key; a
// nil map is a no-op that still evaluates both — the machine op's rule).
func (e *emitter) emitDeleteStmt(c *ast.CallExpr) (any, error) {
	if len(c.Args) != 2 {
		return nil, unsup("delete with %d arguments", len(c.Args))
	}
	mt, ok := e.info.TypeOf(c.Args[0]).Underlying().(*types.Map)
	if !ok {
		return nil, unsup("delete on non-map")
	}
	base, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, err
	}
	index, err := e.emitExpr(c.Args[1])
	if err != nil {
		return nil, err
	}
	keyTy, err := e.emitType(mt.Key())
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "map-delete", "base": base, "index": index, "keyType": keyTy}, nil
}

// emitClearStmt lowers `clear(m)` / `clear(s)` onto the machine's clear ops.
func (e *emitter) emitClearStmt(c *ast.CallExpr) (any, error) {
	if len(c.Args) != 1 {
		return nil, unsup("clear with %d arguments", len(c.Args))
	}
	base, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, err
	}
	switch u := e.info.TypeOf(c.Args[0]).Underlying().(type) {
	case *types.Map:
		return map[string]any{"stmt": "clear-map", "base": base}, nil
	case *types.Slice:
		elemTy, err := e.emitType(u.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "clear-slice", "base": base, "elem": elemTy}, nil
	default:
		return nil, unsup("clear on %s", e.info.TypeOf(c.Args[0]))
	}
}

// deferNoopName is the synthetic function a `defer recover()` defers — a Go
// identifier cannot contain '$', so it cannot collide with user functions.
const deferNoopName = "$deferRecoverNoop"

// emitDeferNoop defers the synthetic empty function, registering it once.
func (e *emitter) emitDeferNoop() any {
	if !e.deferNoopEmitted {
		e.deferNoopEmitted = true
		e.lifted = append(e.lifted, map[string]any{
			"name": deferNoopName, "params": []any{}, "results": []any{},
			"body": map[string]any{"stmt": "block", "body": []any{}},
		})
	}
	return map[string]any{"stmt": "defer",
		"callee": map[string]any{"expr": "func-value", "func": deferNoopName,
			"captured": []any{}},
		"args": []any{}}
}

// isByteSlice reports whether an underlying type is []byte/[]uint8.
func isByteSlice(t types.Type) bool {
	sl, ok := t.(*types.Slice)
	if !ok {
		return false
	}
	b, ok := sl.Elem().Underlying().(*types.Basic)
	return ok && b.Kind() == types.Uint8
}

// isStringType reports whether an underlying type is string.
func isStringType(t types.Type) bool {
	b, ok := t.(*types.Basic)
	return ok && b.Info()&types.IsString != 0
}

// byteSliceOrWrappedString emits a []byte-typed operand: a string-typed
// expression wraps in the []byte conversion (append(b, s...) and
// copy(b, s) read the string's bytes; the fresh backing is invisible —
// the operand is only read).
func (e *emitter) byteSliceOrWrappedString(x ast.Expr) (any, error) {
	w, err := e.emitExpr(x)
	if err != nil {
		return nil, err
	}
	if isStringType(e.info.TypeOf(x).Underlying()) {
		return map[string]any{"expr": "bytes-from-string", "x": w}, nil
	}
	return w, nil
}

// emitAppend hoists append(s, ...) into an "append" statement bound to a
// temp (the machine's appendSlice op: target, base slice, elems slice).
// Non-spread arguments pack into a slice literal exactly like variadic
// packing; a spread argument passes through (a string spread wraps as
// []byte).
func (e *emitter) emitAppend(c *ast.CallExpr) (any, bool, error) {
	if e.hoistForbidden != "" {
		return nil, false, unsup("append in %s", e.hoistForbidden)
	}
	if len(c.Args) == 0 {
		return nil, false, unsup("append with no arguments")
	}
	resTy := e.info.TypeOf(c)
	sl, ok := resTy.Underlying().(*types.Slice)
	if !ok {
		return nil, false, unsup("append result is not a slice")
	}
	elemTy, err := e.emitType(sl.Elem())
	if err != nil {
		return nil, false, err
	}
	base, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, false, err
	}
	var elems any
	if c.Ellipsis != token.NoPos {
		if len(c.Args) != 2 {
			return nil, false, unsup("append spread with %d arguments", len(c.Args))
		}
		elems, err = e.byteSliceOrWrappedString(c.Args[1])
		if err != nil {
			return nil, false, err
		}
	} else {
		packed := []any{}
		for i := 1; i < len(c.Args); i++ {
			if err := e.implicitInterfaceConversionGuard(
				sl.Elem(), e.info.TypeOf(c.Args[i])); err != nil {
				return nil, false, err
			}
			w, err := e.emitExpr(c.Args[i])
			if err != nil {
				return nil, false, err
			}
			packed = append(packed, map[string]any{"index": int64(i - 1), "value": w})
		}
		elems, err = e.hoistSliceLit(packed, elemTy, int64(len(c.Args)-1))
		if err != nil {
			return nil, false, err
		}
	}
	ty, err := e.emitType(resTy)
	if err != nil {
		return nil, false, err
	}
	name := "$c" + itoa(e.tmpSeq)
	e.tmpSeq++
	e.hoisted = append(e.hoisted, map[string]any{
		"stmt":   "append",
		"target": map[string]any{"target": "declare", "id": name, "type": ty},
		"elem":   elemTy,
		"slice":  base,
		"elems":  elems,
	})
	return map[string]any{"expr": "ident", "name": name, "type": ty}, false, nil
}

// emitCopy hoists copy(dst, src) into a "copy" statement whose temp holds
// the copied count (a string source wraps as []byte).
func (e *emitter) emitCopy(c *ast.CallExpr) (any, bool, error) {
	if e.hoistForbidden != "" {
		return nil, false, unsup("copy in %s", e.hoistForbidden)
	}
	if len(c.Args) != 2 {
		return nil, false, unsup("copy with %d arguments", len(c.Args))
	}
	dst, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, false, err
	}
	src, err := e.byteSliceOrWrappedString(c.Args[1])
	if err != nil {
		return nil, false, err
	}
	name := "$c" + itoa(e.tmpSeq)
	e.tmpSeq++
	intTy := intType("int")
	e.hoisted = append(e.hoisted, map[string]any{
		"stmt":   "copy",
		"target": map[string]any{"target": "declare", "id": name, "type": intTy},
		"dst":    dst,
		"src":    src,
	})
	return map[string]any{"expr": "ident", "name": name, "type": intTy}, false, nil
}

// emitMake hoists make([]T, len[, cap]) / make(map[K]V[, hint]) into a
// makeSlice/makeMap statement bound to a temp and returns the temp reference
// (already hoisted, so pure to the caller).
func (e *emitter) emitMake(c *ast.CallExpr) (any, bool, error) {
	if e.hoistForbidden != "" {
		return nil, false, unsup("make in %s", e.hoistForbidden)
	}
	t := e.info.TypeOf(c.Args[0])
	ty, err := e.emitType(t)
	if err != nil {
		return nil, false, err
	}
	name := "$c" + itoa(e.tmpSeq)
	e.tmpSeq++
	target := map[string]any{"target": "declare", "id": name, "type": ty}
	ref := map[string]any{"expr": "ident", "name": name, "type": ty}
	switch u := t.Underlying().(type) {
	case *types.Slice:
		elemTy, err := e.emitType(u.Elem())
		if err != nil {
			return nil, false, err
		}
		lenArg, err := e.emitExpr(c.Args[1])
		if err != nil {
			return nil, false, err
		}
		node := map[string]any{"stmt": "make-slice", "target": target, "elem": elemTy, "len": lenArg}
		if len(c.Args) >= 3 {
			capArg, err := e.emitExpr(c.Args[2])
			if err != nil {
				return nil, false, err
			}
			node["cap"] = capArg
		}
		e.hoisted = append(e.hoisted, node)
		return ref, false, nil
	case *types.Map:
		keyTy, err := e.emitType(u.Key())
		if err != nil {
			return nil, false, err
		}
		valTy, err := e.emitType(u.Elem())
		if err != nil {
			return nil, false, err
		}
		e.hoisted = append(e.hoisted, map[string]any{"stmt": "make-map", "target": target, "keyType": keyTy, "valueType": valTy})
		return ref, false, nil
	default:
		return nil, false, unsup("make of %s", t)
	}
}

func (e *emitter) emitArgs(as []ast.Expr) ([]any, error) {
	args := []any{}
	for _, a := range as {
		w, err := e.emitExpr(a)
		if err != nil {
			return nil, err
		}
		args = append(args, w)
	}
	return args, nil
}

// ---- operator tables ----

func binaryOp(t token.Token) (string, bool) {
	m := map[token.Token]string{
		token.ADD: "+", token.SUB: "-", token.MUL: "*", token.QUO: "/", token.REM: "%",
		token.AND: "&", token.OR: "|", token.XOR: "^", token.AND_NOT: "&^",
		token.SHL: "<<", token.SHR: ">>",
		token.LAND: "&&", token.LOR: "||",
		token.EQL: "==", token.NEQ: "!=", token.LSS: "<", token.LEQ: "<=", token.GTR: ">", token.GEQ: ">=",
	}
	s, ok := m[t]
	return s, ok
}

func compoundOp(t token.Token) (string, bool) {
	m := map[token.Token]string{
		token.ADD_ASSIGN: "+", token.SUB_ASSIGN: "-", token.MUL_ASSIGN: "*",
		token.QUO_ASSIGN: "/", token.REM_ASSIGN: "%",
		token.AND_ASSIGN: "&", token.OR_ASSIGN: "|", token.XOR_ASSIGN: "^", token.AND_NOT_ASSIGN: "&^",
		token.SHL_ASSIGN: "<<", token.SHR_ASSIGN: ">>",
	}
	s, ok := m[t]
	return s, ok
}

func isComparison(op string) bool {
	switch op {
	case "==", "!=", "<", "<=", ">", ">=":
		return true
	}
	return false
}

func declTok(st *ast.DeclStmt) string {
	if gd, ok := st.Decl.(*ast.GenDecl); ok {
		return gd.Tok.String()
	}
	return "?"
}

func itoa(i int) string {
	if i == 0 {
		return "0"
	}
	neg := i < 0
	if neg {
		i = -i
	}
	var b []byte
	for i > 0 {
		b = append([]byte{byte('0' + i%10)}, b...)
		i /= 10
	}
	if neg {
		b = append([]byte{'-'}, b...)
	}
	return string(b)
}
