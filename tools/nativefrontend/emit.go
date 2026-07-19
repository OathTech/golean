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
		fn["recv"] = map[string]any{"id": localName(recv), "type": rty}
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
		w, err := e.emitStmt(s)
		if err != nil {
			return nil, err
		}
		out = append(out, w)
	}
	return out, nil
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
	case *ast.IncDecStmt:
		return e.emitIncDec(st)
	case *ast.ExprStmt:
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
		lhs, err := e.emitExpr(st.Lhs[0])
		if err != nil {
			return nil, err
		}
		rhs, err := e.emitExpr(st.Rhs[0])
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "compound-assign", "op": op, "lhs": lhs, "rhs": rhs}, nil
	}

	lhs := []any{}
	for _, l := range st.Lhs {
		w, err := e.emitAssignTarget(l, define)
		if err != nil {
			return nil, err
		}
		lhs = append(lhs, w)
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
	// Non-ident lvalue (field, index, deref): reuse expression emission; the
	// Lean side turns it into an addressable location.
	expr, err := e.emitExpr(l)
	if err != nil {
		return nil, err
	}
	return map[string]any{"target": "lvalue", "expr": expr}, nil
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
		cond, err := e.emitExpr(st.Cond)
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

func (e *emitter) emitIncDec(st *ast.IncDecStmt) (any, error) {
	x, err := e.emitExpr(st.X)
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
	return map[string]any{"stmt": "incdec", "op": op, "x": x, "type": ty}, nil
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
		return e.emitUnary(ex)
	case *ast.CallExpr:
		return e.emitCall(ex)
	default:
		return nil, unsup("expression %T at %s", x, e.fset.Position(x.Pos()))
	}
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
		return map[string]any{"expr": "int", "value": tv.Value.ExactString()}, nil
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
	y, err := e.emitExpr(b.Y)
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

func (e *emitter) emitCall(c *ast.CallExpr) (any, error) {
	// A "call" whose callee position is a type is a conversion T(x). go/types
	// records this on the callee expression.
	if tv, ok := e.info.Types[c.Fun]; ok && tv.IsType() {
		if len(c.Args) != 1 {
			return nil, unsup("conversion with %d arguments", len(c.Args))
		}
		target, err := e.emitType(e.info.TypeOf(c))
		if err != nil {
			return nil, err
		}
		arg, err := e.emitExpr(c.Args[0])
		if err != nil {
			return nil, err
		}
		return map[string]any{"expr": "convert", "target": target, "x": arg}, nil
	}

	fnID, ok := c.Fun.(*ast.Ident)
	if !ok {
		return nil, unsup("call target %T", c.Fun)
	}
	switch e.info.Uses[fnID].(type) {
	case *types.Func:
		// direct call, handled below
	case *types.Builtin:
		return nil, unsup("builtin %s", fnID.Name)
	default:
		return nil, unsup("call to non-function %s", fnID.Name)
	}
	args := []any{}
	for _, a := range c.Args {
		w, err := e.emitExpr(a)
		if err != nil {
			return nil, err
		}
		args = append(args, w)
	}
	return map[string]any{"expr": "call", "func": fnID.Name, "args": args}, nil
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
