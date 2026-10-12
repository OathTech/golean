package main

// uintptr.go — the STATIC twin of tools/nativefrontend/uintptrid.go (FR-38,
// BUG-124; release-readiness item 26, fix round LOW-2, 2026-10-12): the
// frontend refuses BY NAME every position where `uintptr`'s runtime type
// identity would be observed — (a) a value whose static type mentions
// `uintptr` boxed into an interface (explicitly or at any assignability
// position), (b) a type assertion / type-switch case whose target mentions
// it — because the decoder realizes `uintptr` as `uint64`. Without this
// rule the static judge predicted `lowers(static)` for every such program.
//
// Same rule, same keys (the construct phrase the dynamic row keys on, `$1`),
// same scope (per declaration): a NAMED concrete type is nominal on the
// machine and counts only through its full method set (exported methods
// only for a non-local package — the frontend's "opaque" predicate; here
// every non-local package, source-through stdlib included, is export data,
// so a source-through unit's UNEXPORTED method mentioning uintptr is not
// judged: the measured direction, an under-approximation); an unnamed
// composite is structural; a named interface is its requirements. Generic
// TEMPLATES are not judged (the frontend scans each stencil under its
// instantiation; a template is quarantined by design).

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
)

const uintptrCauseID = "uintptr-identity"

type uintptrScan struct {
	a       *analyzer
	d       *declReport
	results []*types.Tuple
}

// uintptrIdentity judges one non-generic function body (or one initializer
// statement) and adds a `uintptr-identity` finding per construct found.
func (a *analyzer) uintptrIdentity(d *declReport, body ast.Node, results *types.Tuple) {
	if body == nil || d.IsGeneric {
		return
	}
	if blk, ok := body.(*ast.BlockStmt); ok && blk == nil {
		return
	}
	s := &uintptrScan{a: a, d: d}
	s.walk(body, results)
}

func (s *uintptrScan) typeOf(x ast.Expr) types.Type {
	return s.a.info.TypeOf(x)
}

func (s *uintptrScan) add(construct string, at ast.Node) {
	s.d.add(finding{Cause: mustCause(uintptrCauseID), Key: construct, Pos: s.a.p.pos(at), Certain: true})
}

func (s *uintptrScan) mentions(t types.Type, seen map[*types.Named]bool) bool {
	if seen == nil {
		seen = map[*types.Named]bool{}
	}
	switch ty := t.(type) {
	case nil:
		return false
	case *types.Basic:
		return ty.Kind() == types.Uintptr
	case *types.Alias:
		return s.mentions(types.Unalias(ty), seen)
	case *types.Named:
		if seen[ty] {
			return false
		}
		seen[ty] = true
		if _, isIface := ty.Underlying().(*types.Interface); isIface {
			return s.mentions(ty.Underlying(), seen)
		}
		ms := types.NewMethodSet(types.NewPointer(ty))
		for i := 0; i < ms.Len(); i++ {
			m, ok := ms.At(i).Obj().(*types.Func)
			// Per method: an unexported method of a non-local package is
			// nameable by no requirement in the judged program.
			if !ok || (!m.Exported() && (m.Pkg() == nil || !s.a.p.isLocalPkg(m.Pkg()))) {
				continue
			}
			if s.mentions(m.Type(), seen) {
				return true
			}
		}
		if targs := ty.TypeArgs(); targs != nil {
			for i := 0; i < targs.Len(); i++ {
				if s.mentions(targs.At(i), seen) {
					return true
				}
			}
		}
		return false
	case *types.Pointer:
		return s.mentions(ty.Elem(), seen)
	case *types.Slice:
		return s.mentions(ty.Elem(), seen)
	case *types.Array:
		return s.mentions(ty.Elem(), seen)
	case *types.Chan:
		return s.mentions(ty.Elem(), seen)
	case *types.Map:
		return s.mentions(ty.Key(), seen) || s.mentions(ty.Elem(), seen)
	case *types.Struct:
		for i := 0; i < ty.NumFields(); i++ {
			if s.mentions(ty.Field(i).Type(), seen) {
				return true
			}
		}
	case *types.Tuple:
		for i := 0; i < ty.Len(); i++ {
			if s.mentions(ty.At(i).Type(), seen) {
				return true
			}
		}
	case *types.Signature:
		return s.mentions(ty.Params(), seen) || s.mentions(ty.Results(), seen)
	case *types.Interface:
		for i := 0; i < ty.NumMethods(); i++ {
			if s.mentions(ty.Method(i).Type(), seen) {
				return true
			}
		}
	}
	return false
}

func (s *uintptrScan) boxType(target, src types.Type, at ast.Node, what string) {
	if target == nil || src == nil || !types.IsInterface(target) || types.IsInterface(src) || !s.mentions(src, nil) {
		return
	}
	s.add(fmt.Sprintf("%s boxes %s into %s", what, typeStr(src), typeStr(target)), at)
}

func (s *uintptrScan) box(target types.Type, src ast.Expr, what string) {
	if src != nil {
		s.boxType(target, s.typeOf(src), src, what)
	}
}

func (s *uintptrScan) target(texpr ast.Expr, what string) {
	if t := s.typeOf(texpr); t != nil && s.mentions(t, nil) {
		s.add(fmt.Sprintf("%s %s", what, typeStr(t)), texpr)
	}
}

func underlyingOf(t types.Type) types.Type {
	if t == nil {
		return nil
	}
	return t.Underlying()
}

func (s *uintptrScan) components(x ast.Expr) []types.Type {
	t := s.typeOf(x)
	if tup, ok := t.(*types.Tuple); ok {
		out := make([]types.Type, tup.Len())
		for i := range out {
			out[i] = tup.At(i).Type()
		}
		return out
	}
	switch u := ast.Unparen(x).(type) {
	case *ast.TypeAssertExpr:
		if u.Type != nil {
			return []types.Type{s.typeOf(u.Type), types.Typ[types.Bool]}
		}
	case *ast.IndexExpr:
		if m, ok := underlyingOf(s.typeOf(u.X)).(*types.Map); ok {
			return []types.Type{m.Elem(), types.Typ[types.Bool]}
		}
	case *ast.UnaryExpr:
		if u.Op == token.ARROW {
			if ch, ok := underlyingOf(s.typeOf(u.X)).(*types.Chan); ok {
				return []types.Type{ch.Elem(), types.Typ[types.Bool]}
			}
		}
	}
	if t == nil {
		return nil
	}
	return []types.Type{t}
}

func (s *uintptrScan) walk(root ast.Node, results *types.Tuple) {
	s.results = append(s.results, results)
	defer func() { s.results = s.results[:len(s.results)-1] }()
	ast.Inspect(root, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.FuncLit:
			var res *types.Tuple
			if sig, ok := s.typeOf(x).(*types.Signature); ok {
				res = sig.Results()
			}
			s.walk(x.Body, res)
			return false
		case *ast.AssignStmt:
			s.assign(x)
		case *ast.ValueSpec:
			s.valueSpec(x)
		case *ast.ReturnStmt:
			s.ret(x)
		case *ast.CallExpr:
			s.call(x)
		case *ast.CompositeLit:
			s.composite(x)
		case *ast.SendStmt:
			if ch, ok := underlyingOf(s.typeOf(x.Chan)).(*types.Chan); ok {
				s.box(ch.Elem(), x.Value, "send")
			}
		case *ast.IndexExpr:
			if m, ok := underlyingOf(s.typeOf(x.X)).(*types.Map); ok {
				s.box(m.Key(), x.Index, "map index key")
			}
		case *ast.BinaryExpr:
			if x.Op == token.EQL || x.Op == token.NEQ {
				tx, ty := s.typeOf(x.X), s.typeOf(x.Y)
				switch {
				case tx == nil || ty == nil:
				case types.IsInterface(tx) && !types.IsInterface(ty):
					s.boxType(tx, ty, x.Y, "comparison operand")
				case types.IsInterface(ty) && !types.IsInterface(tx):
					s.boxType(ty, tx, x.X, "comparison operand")
				}
			}
		case *ast.SwitchStmt:
			s.switchStmt(x)
		case *ast.TypeAssertExpr:
			if x.Type != nil {
				s.target(x.Type, "type assertion to")
			}
		case *ast.TypeSwitchStmt:
			for _, raw := range x.Body.List {
				if cc, ok := raw.(*ast.CaseClause); ok {
					for _, te := range cc.List {
						s.target(te, "type switch case")
					}
				}
			}
		case *ast.RangeStmt:
			s.rangeStmt(x)
		}
		return true
	})
}

func (s *uintptrScan) assign(x *ast.AssignStmt) {
	if x.Tok != token.ASSIGN && x.Tok != token.DEFINE {
		return
	}
	if len(x.Lhs) == len(x.Rhs) {
		for i, l := range x.Lhs {
			s.box(s.typeOf(l), x.Rhs[i], "assignment")
		}
		return
	}
	if len(x.Rhs) != 1 {
		return
	}
	comps := s.components(x.Rhs[0])
	for i, l := range x.Lhs {
		if i < len(comps) {
			s.boxType(s.typeOf(l), comps[i], x.Rhs[0], "multi-value assignment")
		}
	}
}

func (s *uintptrScan) valueSpec(x *ast.ValueSpec) {
	if len(x.Values) == 0 {
		return
	}
	targetOf := func(i int) types.Type {
		if x.Type != nil {
			return s.typeOf(x.Type)
		}
		return s.typeOf(x.Names[i])
	}
	if len(x.Values) == len(x.Names) {
		for i := range x.Names {
			s.box(targetOf(i), x.Values[i], "variable declaration")
		}
		return
	}
	if len(x.Values) != 1 {
		return
	}
	comps := s.components(x.Values[0])
	for i := range x.Names {
		if i < len(comps) {
			s.boxType(targetOf(i), comps[i], x.Values[0], "multi-value variable declaration")
		}
	}
}

func (s *uintptrScan) ret(x *ast.ReturnStmt) {
	if len(x.Results) == 0 || len(s.results) == 0 {
		return
	}
	res := s.results[len(s.results)-1]
	if res == nil {
		return
	}
	if len(x.Results) == res.Len() {
		for i, r := range x.Results {
			s.box(res.At(i).Type(), r, "return")
		}
		return
	}
	if len(x.Results) != 1 {
		return
	}
	comps := s.components(x.Results[0])
	for i := 0; i < res.Len() && i < len(comps); i++ {
		s.boxType(res.At(i).Type(), comps[i], x.Results[0], "multi-value return")
	}
}

func (s *uintptrScan) builtinName(fun ast.Expr) string {
	switch f := ast.Unparen(fun).(type) {
	case *ast.Ident:
		if b, ok := s.a.info.Uses[f].(*types.Builtin); ok {
			return b.Name()
		}
	case *ast.SelectorExpr:
		if b, ok := s.a.info.Uses[f.Sel].(*types.Builtin); ok {
			return b.Name()
		}
	}
	return ""
}

func (s *uintptrScan) call(x *ast.CallExpr) {
	tv, ok := s.a.info.Types[x.Fun]
	if ok && tv.IsType() {
		if len(x.Args) == 1 {
			s.box(tv.Type, x.Args[0], "conversion")
		}
		return
	}
	if ok && tv.IsBuiltin() {
		switch s.builtinName(x.Fun) {
		case "append":
			if x.Ellipsis != token.NoPos || len(x.Args) < 2 {
				return
			}
			if sl, ok := underlyingOf(s.typeOf(x)).(*types.Slice); ok {
				for _, a := range x.Args[1:] {
					s.box(sl.Elem(), a, "append element")
				}
			}
		case "delete":
			if len(x.Args) == 2 {
				if m, ok := underlyingOf(s.typeOf(x.Args[0])).(*types.Map); ok {
					s.box(m.Key(), x.Args[1], "delete key")
				}
			}
		case "panic":
			if len(x.Args) == 1 {
				s.box(types.Universe.Lookup("any").Type(), x.Args[0], "panic value")
			}
		}
		return
	}
	sig, ok := underlyingOf(s.typeOf(x.Fun)).(*types.Signature)
	if !ok {
		return
	}
	params := sig.Params()
	np := params.Len()
	paramAt := func(i int) types.Type {
		if sig.Variadic() && i >= np-1 {
			last := params.At(np - 1).Type()
			if x.Ellipsis != token.NoPos {
				return last
			}
			if sl, ok := last.(*types.Slice); ok {
				return sl.Elem()
			}
			return last
		}
		if i < np {
			return params.At(i).Type()
		}
		return nil
	}
	if len(x.Args) == 1 {
		if tup, ok := s.typeOf(x.Args[0]).(*types.Tuple); ok {
			for i := 0; i < tup.Len(); i++ {
				s.boxType(paramAt(i), tup.At(i).Type(), x.Args[0], "call argument")
			}
			return
		}
	}
	for i, a := range x.Args {
		s.box(paramAt(i), a, "call argument")
	}
}

func (s *uintptrScan) composite(x *ast.CompositeLit) {
	t := s.typeOf(x)
	if t == nil {
		return
	}
	u := t.Underlying()
	if p, ok := u.(*types.Pointer); ok {
		u = p.Elem().Underlying()
	}
	switch u := u.(type) {
	case *types.Struct:
		for i, elt := range x.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				if key, ok := kv.Key.(*ast.Ident); ok {
					for j := 0; j < u.NumFields(); j++ {
						if u.Field(j).Name() == key.Name {
							s.box(u.Field(j).Type(), kv.Value, "struct literal field "+key.Name)
							break
						}
					}
				}
				continue
			}
			if i < u.NumFields() {
				s.box(u.Field(i).Type(), elt, "struct literal field "+u.Field(i).Name())
			}
		}
	case *types.Array:
		for _, elt := range x.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				elt = kv.Value
			}
			s.box(u.Elem(), elt, "array literal element")
		}
	case *types.Slice:
		for _, elt := range x.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				elt = kv.Value
			}
			s.box(u.Elem(), elt, "slice literal element")
		}
	case *types.Map:
		for _, elt := range x.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				s.box(u.Key(), kv.Key, "map literal key")
				s.box(u.Elem(), kv.Value, "map literal value")
			}
		}
	}
}

func (s *uintptrScan) switchStmt(x *ast.SwitchStmt) {
	if x.Tag == nil {
		return
	}
	tt := s.typeOf(x.Tag)
	if tt == nil {
		return
	}
	for _, raw := range x.Body.List {
		cc, ok := raw.(*ast.CaseClause)
		if !ok {
			continue
		}
		for _, ce := range cc.List {
			tc := s.typeOf(ce)
			switch {
			case tc == nil:
			case types.IsInterface(tt) && !types.IsInterface(tc):
				s.boxType(tt, tc, ce, "switch case against an interface tag")
			case types.IsInterface(tc) && !types.IsInterface(tt):
				s.boxType(tc, tt, ce, "switch tag against an interface case")
			}
		}
	}
}

func (s *uintptrScan) rangeStmt(x *ast.RangeStmt) {
	if x.Tok != token.ASSIGN {
		return
	}
	rt := s.typeOf(x.X)
	if rt == nil {
		return
	}
	var kt, vt types.Type
	switch u := rt.Underlying().(type) {
	case *types.Basic:
		if u.Info()&types.IsString != 0 {
			kt, vt = types.Typ[types.Int], types.Typ[types.Rune]
		} else if u.Info()&types.IsInteger != 0 {
			kt = rt
		}
	case *types.Array:
		kt, vt = types.Typ[types.Int], u.Elem()
	case *types.Pointer:
		if arr, ok := u.Elem().Underlying().(*types.Array); ok {
			kt, vt = types.Typ[types.Int], arr.Elem()
		}
	case *types.Slice:
		kt, vt = types.Typ[types.Int], u.Elem()
	case *types.Map:
		kt, vt = u.Key(), u.Elem()
	case *types.Chan:
		kt = u.Elem()
	default:
		return
	}
	isBlank := func(e ast.Expr) bool { id, ok := e.(*ast.Ident); return ok && id.Name == "_" }
	if x.Key != nil && !isBlank(x.Key) {
		s.boxType(s.typeOf(x.Key), kt, x.Key, "range key assignment")
	}
	if x.Value != nil && !isBlank(x.Value) {
		s.boxType(s.typeOf(x.Value), vt, x.Value, "range value assignment")
	}
}
