package main

// emit.go emits functions, statements, and expressions as wire nodes. Every
// expression node carries its resolved go/types type under "type" so the Lean
// lowering always has type information where GoCore needs it. Constructs not
// yet modeled return an unsupported error (fail closed).

import (
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
				fn, err := e.emitFuncDecl(d)
				if err != nil {
					return nil, err
				}
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
		target, err := e.emitLValue(st.Lhs[0])
		if err != nil {
			return nil, err
		}
		read, err := e.emitExpr(st.Lhs[0])
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
	// A single call on the RHS (possibly multi-value) is emitted un-hoisted so
	// the lowering makes it a call statement writing all targets; hoisting would
	// force its result into one temp, which fails for a multi-value return.
	if len(st.Rhs) == 1 {
		if call, ok := st.Rhs[0].(*ast.CallExpr); ok {
			node, effectful, err := e.emitCallNode(call)
			if err != nil {
				return nil, err
			}
			if effectful {
				return map[string]any{"stmt": "assign", "define": define, "lhs": lhs, "rhs": []any{node}}, nil
			}
		}
	}
	rhs := []any{}
	for _, r := range st.Rhs {
		w, err := e.emitExpr(r)
		if err != nil {
			return nil, err
		}
		rhs = append(rhs, w)
	}
	return map[string]any{"stmt": "assign", "define": define, "lhs": lhs, "rhs": rhs}, nil
}

// emitAssignTarget emits an lvalue. On `:=`, a target ident that go/types
// records as a new definition is a declaration (carries its type).
func (e *emitter) emitAssignTarget(l ast.Expr, define bool) (any, error) {
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
				init, err := e.emitExpr(vs.Values[i])
				if err != nil {
					return nil, err
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
		els, err := e.emitStmt(st.Else)
		if err != nil {
			return nil, err
		}
		node["else"] = els
	}
	return node, nil
}

func (e *emitter) emitFor(st *ast.ForStmt) (any, error) {
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
		post, err := e.emitStmt(st.Post)
		if err != nil {
			return nil, err
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

func (e *emitter) emitIncDec(st *ast.IncDecStmt) (any, error) {
	target, err := e.emitLValue(st.X)
	if err != nil {
		return nil, err
	}
	read, err := e.emitExpr(st.X)
	if err != nil {
		return nil, err
	}
	op := "+"
	if st.Tok == token.DEC {
		op = "-"
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
	// A method value / package selector is not a field read; only field
	// selections are handled here (method calls come with the call increment).
	if seln, ok := e.info.Selections[sel]; ok && seln.Kind() != types.FieldVal {
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
	switch ex := x.(type) {
	case *ast.Ident:
		return map[string]any{"expr": "ref", "id": ex.Name}, nil
	case *ast.SelectorExpr:
		base, structName, err := e.fieldBase(ex)
		if err != nil {
			return nil, err
		}
		return map[string]any{"expr": "field-addr", "base": base, "typeId": structName, "field": ex.Sel.Name}, nil
	case *ast.IndexExpr:
		base, err := e.emitExpr(ex.X)
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
		if v, ok := keyed[fld.Name()]; ok {
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
		return map[string]any{"expr": "string", "value": constant.StringVal(tv.Value)}, nil
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
		target, err := e.emitType(e.info.TypeOf(c))
		if err != nil {
			return nil, false, err
		}
		arg, err := e.emitExpr(c.Args[0])
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
	if sig == nil || !sig.Variadic() || c.Ellipsis != token.NoPos {
		return e.emitArgs(c.Args)
	}
	fixed := sig.Params().Len() - 1
	args := []any{}
	for i := 0; i < fixed; i++ {
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
	elems := []any{}
	for i := fixed; i < len(c.Args); i++ {
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
	// Receiver argument: pass the address for a pointer receiver, else the value.
	var recvArg any
	var err error
	if pointerRecv {
		recvArg, err = e.emitAddressOf(sel.X)
	} else {
		recvArg, err = e.emitExpr(sel.X)
	}
	if err != nil {
		return nil, false, err
	}
	args, err := e.emitArgs(c.Args)
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
	default:
		return nil, false, unsup("builtin %s", name)
	}
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
