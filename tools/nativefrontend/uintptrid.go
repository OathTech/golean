package main

// uintptrid.go — `uintptr`'s runtime type IDENTITY is unmodeled, and is
// refused BY NAME at the positions where it would be observed
// (release-readiness punch list item 26, BUG-123; [USER] Mike 2026-10-12,
// verbatim: «D6: agree on both - refuse and repair asap.» — this file is the
// REFUSE half; the repair is the parked `typed-uintptr-identity` work).
//
// THE DEFECT. The decoder maps the wire's `uintptr` to the machine's
// `.uint64` (`GoLean/NativeToIR.lean` `intKindOfName`), so `uintptr` and
// `uint64` are ONE runtime identity: `any(uintptr(1)).(uint64)` comma-ok is
// TRUE (gc: false), `any(uintptr(1)) == any(uint64(1))` is TRUE (gc: false),
// a type switch over a boxed uintptr takes `case uint64` (gc: `case
// uintptr`), `len(map[any]int{uintptr(1): 7, uint64(1): 9})` is 1 (gc: 2),
// and `any([]uintptr{1}).([]uint64)` / `any(&u).(*uint64)` comma-ok are TRUE
// (gc: false) — the release-trust review's six R1 probes
// (`docs/2026-10-12_release-trust-review.md`). WIDTH-only uses — arithmetic,
// conversions, storage, `atomic.*Uintptr`, `println` — are correct and stay
// lowered: 64 bits is the right width (latitude inventory §11 item 6).
//
// WHERE IDENTITY IS OBSERVED. Every runtime comparison of type identities
// takes at least one INTERFACE value (type assertion, type switch,
// interface `==`, `map[I]` key hashing, interface-requirement satisfaction),
// and an interface value whose dynamic type mentions `uintptr` is produced
// only by a CONVERSION of such a value to an interface type — explicit
// (`any(x)`) or implicit at an assignability position (spec#Assignability:
// assignment, `var` initializer, call argument incl. variadic, return,
// composite-literal element/key/field, send, `map[I]` index key, `panic`,
// `append` element, the assignment form of `range`, interface `==`/`!=`,
// `switch` case against an interface tag). The two refusal rules:
//
//   (a) BOXING: a value whose static type MENTIONS `uintptr` — the type
//       itself; a pointer/slice/array/map/chan/struct/func type mentioning
//       it; a defined type over it; a named type whose METHOD SET mentions
//       it (the decoder compares interface requirements by wire types, so
//       `P() uintptr` and `P() uint64` collapse too); a modeled/opaque
//       stdlib type through its method set only (`mentionsUintptr`) —
//       converted to an interface type (not a type parameter after
//       substitution; a stencil body is scanned under its instantiation,
//       `goTypeOf`).
//   (b) TARGET: a type assertion or type-switch case whose target type
//       mentions `uintptr` (it compares identities against a dynamic type).
//
// The dispatch tables are NOT a third entry point: method tables key on the
// receiver's NAMED type and generic instantiations on `renderTypeKey`
// (mono.go), which spells `uintptr` distinctly; the collapse happens only
// at the decoder's IntKind, which (a) and (b) fence at the frontend.
//
// MECHANISM. A per-body pre-pass over the declaration's AST
// (`checkUintptrIdentity`, called from `emitFuncDecl` for every function,
// method and stencil body, and from the package-initializer dry run for
// every `$pkginit` initializer statement — function literals are reached
// inside their enclosing body, with their own result tuple for `return`).
// A hit is the standing per-declaration quarantine (`unsupported`): the
// declaration becomes a stub refused by name when called, the export stays
// OK, the row lands at `frontend-export`. The refusal names the construct,
// its position, the item and the bug, and classifies under
// tools/lowerdiag/causes.tsv `uintptr-identity` (FR-38).

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
)

// uintptrIdentityItem is the pointer every refusal of this file carries.
const uintptrIdentityItem = "release-readiness item 26, BUG-123"

// refuseUintptrIdentity builds the named refusal for one construct at one
// position. The text is the cause table's `uintptr-identity` pattern.
func (e *emitter) refuseUintptrIdentity(construct string, at ast.Node) error {
	return unsup("uintptr identity is unmodeled (lowered as uint64): %s at %s — refused by name pending the typed-uintptr-identity repair (%s)",
		construct, e.fset.Position(at.Pos()), uintptrIdentityItem)
}

// mentionsUintptr reports whether t structurally mentions the basic type
// `uintptr`: through pointers, slices, arrays, channels, maps, struct
// fields, signatures (params and results), interface method signatures,
// a named type's underlying type, type arguments and METHOD SET. `seen`
// breaks recursive named types (`type N struct{ next *N }`). A type
// parameter is never reached from a stencil body (`goTypeOf` substitutes;
// an unsubstituted one is the stencil's own `substErr`); a constraint
// union is not a runtime type.
//
// A named type declared OUTSIDE the source packages (a modeled or opaque
// stdlib type — `sync.Map`, `sync.Mutex`, `atomic.Uintptr`, …) is entered
// through its METHOD SET and type arguments only, never its real
// underlying structure: the machine materializes the frontend's MODEL of
// such a type (importedmodel.go, the sync tables), not go/types' fields
// (`sync.Map`'s hash seed is a `uintptr` the wire never carries), and its
// identity is nominal. Its EXPORTED method signatures ARE on the wire
// (interface requirements compare them), so `atomic.Uintptr`'s `Load()
// uintptr` counts; its unexported ones are nameable by no requirement
// outside their package and do not. Source packages (main, case-local
// imports, source-through stdlib units) are lowered by structure and are
// entered in full, unexported methods included (a same-package interface
// can require them).
func (e *emitter) mentionsUintptr(t types.Type, seen map[*types.Named]bool) bool {
	if seen == nil {
		seen = map[*types.Named]bool{}
	}
	switch ty := t.(type) {
	case nil:
		return false
	case *types.Basic:
		return ty.Kind() == types.Uintptr
	case *types.Alias:
		return e.mentionsUintptr(types.Unalias(ty), seen)
	case *types.Named:
		if seen[ty] {
			return false
		}
		seen[ty] = true
		obj := ty.Obj()
		opaque := obj != nil && obj.Pkg() != nil && !e.isSourcePackage(obj.Pkg())
		if !opaque && e.mentionsUintptr(ty.Underlying(), seen) {
			return true
		}
		for i := 0; i < ty.NumMethods(); i++ {
			m := ty.Method(i)
			if opaque && !m.Exported() {
				// A foreign package's UNEXPORTED method (`log.Logger`'s
				// `output(pc uintptr, …)`, reached from the raft subject's
				// `DefaultLogger` through its embedded `*log.Logger`) is
				// nameable by no interface requirement outside that
				// package — unexported names are package-scoped — so it
				// takes part in no satisfiable identity comparison.
				continue
			}
			if e.mentionsUintptr(m.Type(), seen) {
				return true
			}
		}
		if targs := ty.TypeArgs(); targs != nil {
			for i := 0; i < targs.Len(); i++ {
				if e.mentionsUintptr(targs.At(i), seen) {
					return true
				}
			}
		}
		return false
	case *types.Pointer:
		return e.mentionsUintptr(ty.Elem(), seen)
	case *types.Slice:
		return e.mentionsUintptr(ty.Elem(), seen)
	case *types.Array:
		return e.mentionsUintptr(ty.Elem(), seen)
	case *types.Chan:
		return e.mentionsUintptr(ty.Elem(), seen)
	case *types.Map:
		return e.mentionsUintptr(ty.Key(), seen) || e.mentionsUintptr(ty.Elem(), seen)
	case *types.Struct:
		for i := 0; i < ty.NumFields(); i++ {
			if e.mentionsUintptr(ty.Field(i).Type(), seen) {
				return true
			}
		}
		return false
	case *types.Tuple:
		for i := 0; i < ty.Len(); i++ {
			if e.mentionsUintptr(ty.At(i).Type(), seen) {
				return true
			}
		}
		return false
	case *types.Signature:
		return e.mentionsUintptr(ty.Params(), seen) || e.mentionsUintptr(ty.Results(), seen)
	case *types.Interface:
		for i := 0; i < ty.NumMethods(); i++ {
			if e.mentionsUintptr(ty.Method(i).Type(), seen) {
				return true
			}
		}
		return false
	case *types.TypeParam, *types.Union:
		return false
	}
	return false
}

// uintptrTypeString renders a type for the refusal text with package NAMES
// (`main.U`), the display the frontend's other refusals use.
func uintptrTypeString(t types.Type) string {
	return types.TypeString(t, func(p *types.Package) string { return p.Name() })
}

// uintptrIdentityScan is one declaration body's pre-pass state: the stack
// of enclosing result tuples (the declaration's, then each nested function
// literal's) for `return`, and the first refusal found.
type uintptrIdentityScan struct {
	e       *emitter
	results []*types.Tuple
	err     error
}

// checkUintptrIdentity scans one body (a function declaration's block, or
// one synthesized `$pkginit` initializer statement) and returns the first
// identity-bearing position as the declaration's `unsupported` refusal.
// `results` is the enclosing signature's result tuple (nil for `$pkginit`,
// which has no result slots).
func (e *emitter) checkUintptrIdentity(body ast.Node, results *types.Tuple) error {
	if body == nil {
		return nil
	}
	if blk, ok := body.(*ast.BlockStmt); ok && blk == nil {
		// A BODYLESS declaration (an assembly-backed library function such
		// as internal/bytealg's, reached through a source-through unit):
		// nothing to scan. A typed nil inside the interface is not `== nil`
		// — the first cut crashed ast.Inspect on exactly this (the
		// stdlib-source/frontier package, lane gate 2026-10-12).
		return nil
	}
	s := &uintptrIdentityScan{e: e}
	s.walk(body, results)
	return s.err
}

// typeOf is the substitution-aware type of an expression, nil when go/types
// recorded none (a blank identifier on an assignment's left side).
func (s *uintptrIdentityScan) typeOf(x ast.Expr) types.Type {
	t := s.e.info.TypeOf(x)
	if t == nil {
		return nil
	}
	return s.e.applySubst(t)
}

func (s *uintptrIdentityScan) walk(root ast.Node, results *types.Tuple) {
	s.results = append(s.results, results)
	defer func() { s.results = s.results[:len(s.results)-1] }()
	ast.Inspect(root, func(n ast.Node) bool {
		if s.err != nil {
			return false
		}
		switch x := n.(type) {
		case *ast.FuncLit:
			// The literal's own body returns against ITS results; the
			// enclosing walk does not descend (Inspect stops here).
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
			if ch, ok := s.underlying(s.typeOf(x.Chan)).(*types.Chan); ok {
				s.box(ch.Elem(), x.Value, "send")
			}
		case *ast.IndexExpr:
			if m, ok := s.underlying(s.typeOf(x.X)).(*types.Map); ok {
				s.box(m.Key(), x.Index, "map index key")
			}
		case *ast.BinaryExpr:
			if x.Op == token.EQL || x.Op == token.NEQ {
				s.compare(x)
			}
		case *ast.SwitchStmt:
			s.switchStmt(x)
		case *ast.TypeAssertExpr:
			if x.Type != nil {
				s.target(x.Type, "type assertion to")
			}
		case *ast.TypeSwitchStmt:
			for _, raw := range x.Body.List {
				cc, ok := raw.(*ast.CaseClause)
				if !ok {
					continue
				}
				for _, te := range cc.List {
					s.target(te, "type switch case")
				}
			}
		case *ast.RangeStmt:
			s.rangeStmt(x)
		}
		return s.err == nil
	})
}

// underlying is the underlying type of t, nil-safe.
func (s *uintptrIdentityScan) underlying(t types.Type) types.Type {
	if t == nil {
		return nil
	}
	return t.Underlying()
}

// boxType is rule (a) on a known source type: a non-interface source
// mentioning `uintptr` converted to an interface target refuses, named
// `what` at `at`.
func (s *uintptrIdentityScan) boxType(target, src types.Type, at ast.Node, what string) {
	if s.err != nil || target == nil || src == nil {
		return
	}
	if !types.IsInterface(target) || types.IsInterface(src) {
		return
	}
	if !s.e.mentionsUintptr(src, nil) {
		return
	}
	s.err = s.e.refuseUintptrIdentity(fmt.Sprintf("%s boxes %s into %s", what,
		uintptrTypeString(src), uintptrTypeString(target)), at)
}

// box is rule (a) on a source expression.
func (s *uintptrIdentityScan) box(target types.Type, src ast.Expr, what string) {
	if src == nil {
		return
	}
	s.boxType(target, s.typeOf(src), src, what)
}

// target is rule (b): an assertion / type-switch target type that mentions
// `uintptr`.
func (s *uintptrIdentityScan) target(texpr ast.Expr, what string) {
	if s.err != nil {
		return
	}
	t := s.typeOf(texpr)
	if t == nil || !s.e.mentionsUintptr(t, nil) {
		return
	}
	s.err = s.e.refuseUintptrIdentity(fmt.Sprintf("%s %s", what, uintptrTypeString(t)), texpr)
}

// components lists the value types a single right-hand expression yields in
// a multi-target context: a tuple-typed call's elements, or the two values
// of a comma-ok assertion / map index / receive (go/types records the
// single-value type for those; the second is `bool`).
func (s *uintptrIdentityScan) components(x ast.Expr) []types.Type {
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
		if m, ok := s.underlying(s.typeOf(u.X)).(*types.Map); ok {
			return []types.Type{m.Elem(), types.Typ[types.Bool]}
		}
	case *ast.UnaryExpr:
		if u.Op == token.ARROW {
			if ch, ok := s.underlying(s.typeOf(u.X)).(*types.Chan); ok {
				return []types.Type{ch.Elem(), types.Typ[types.Bool]}
			}
		}
	}
	if t == nil {
		return nil
	}
	return []types.Type{t}
}

func isBlankIdent(x ast.Expr) bool {
	id, ok := x.(*ast.Ident)
	return ok && id.Name == "_"
}

func (s *uintptrIdentityScan) assign(x *ast.AssignStmt) {
	if x.Tok != token.ASSIGN && x.Tok != token.DEFINE {
		return // `op=` never converts (operators take no interface operand)
	}
	if len(x.Lhs) == len(x.Rhs) {
		for i, l := range x.Lhs {
			if isBlankIdent(l) {
				continue
			}
			s.box(s.typeOf(l), x.Rhs[i], "assignment")
		}
		return
	}
	if len(x.Rhs) != 1 {
		return
	}
	comps := s.components(x.Rhs[0])
	for i, l := range x.Lhs {
		if i >= len(comps) || isBlankIdent(l) {
			continue
		}
		s.boxType(s.typeOf(l), comps[i], x.Rhs[0], "multi-value assignment")
	}
}

func (s *uintptrIdentityScan) valueSpec(x *ast.ValueSpec) {
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
		if i >= len(comps) {
			continue
		}
		s.boxType(targetOf(i), comps[i], x.Values[0], "multi-value variable declaration")
	}
}

func (s *uintptrIdentityScan) ret(x *ast.ReturnStmt) {
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

// builtinName is the name of a builtin callee (`append`, `panic`, …), or "".
func (s *uintptrIdentityScan) builtinName(fun ast.Expr) string {
	switch f := ast.Unparen(fun).(type) {
	case *ast.Ident:
		if b, ok := s.e.info.Uses[f].(*types.Builtin); ok {
			return b.Name()
		}
	case *ast.SelectorExpr:
		if b, ok := s.e.info.Uses[f.Sel].(*types.Builtin); ok {
			return b.Name()
		}
	}
	return ""
}

func (s *uintptrIdentityScan) call(x *ast.CallExpr) {
	tv, ok := s.e.typesEntry(x.Fun)
	if ok && tv.IsType() {
		// A conversion: `any(v)`, `I(v)` — the explicit boxing.
		if len(x.Args) == 1 {
			s.box(tv.Type, x.Args[0], "conversion")
		}
		return
	}
	if ok && tv.IsBuiltin() {
		switch s.builtinName(x.Fun) {
		case "append":
			if x.Ellipsis != token.NoPos || len(x.Args) < 2 {
				return // `append(s, t...)` passes a slice whole: no element conversion
			}
			if sl, ok := s.underlying(s.typeOf(x)).(*types.Slice); ok {
				for _, a := range x.Args[1:] {
					s.box(sl.Elem(), a, "append element")
				}
			}
		case "delete":
			if len(x.Args) == 2 {
				if m, ok := s.underlying(s.typeOf(x.Args[0])).(*types.Map); ok {
					s.box(m.Key(), x.Args[1], "delete key")
				}
			}
		case "panic":
			// `panic(v any)`: the value is boxed and recoverable as `any`.
			if len(x.Args) == 1 {
				s.box(types.Universe.Lookup("any").Type(), x.Args[0], "panic value")
			}
		}
		return
	}
	sig, ok := s.underlying(s.typeOf(x.Fun)).(*types.Signature)
	if !ok {
		return
	}
	params := sig.Params()
	np := params.Len()
	paramAt := func(i int) types.Type {
		if sig.Variadic() && i >= np-1 {
			last := params.At(np - 1).Type()
			if x.Ellipsis != token.NoPos {
				return last // `f(s...)`: the slice is passed whole
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
			// `f(g())` with a multi-valued g: each component to its parameter.
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

func (s *uintptrIdentityScan) composite(x *ast.CompositeLit) {
	t := s.typeOf(x)
	if t == nil {
		return
	}
	u := t.Underlying()
	if p, ok := u.(*types.Pointer); ok {
		// An elided `&T{…}` element of a `[]*T{{…}}` literal.
		u = p.Elem().Underlying()
	}
	switch u := u.(type) {
	case *types.Struct:
		for i, elt := range x.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				key, ok := kv.Key.(*ast.Ident)
				if !ok {
					continue
				}
				for j := 0; j < u.NumFields(); j++ {
					if u.Field(j).Name() == key.Name {
						s.box(u.Field(j).Type(), kv.Value, "struct literal field "+key.Name)
						break
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
			kv, ok := elt.(*ast.KeyValueExpr)
			if !ok {
				continue
			}
			s.box(u.Key(), kv.Key, "map literal key")
			s.box(u.Elem(), kv.Value, "map literal value")
		}
	}
}

// compare is `==` / `!=` with exactly one interface operand: the other is
// converted to that interface type (spec#Comparison_operators).
func (s *uintptrIdentityScan) compare(x *ast.BinaryExpr) {
	tx, ty := s.typeOf(x.X), s.typeOf(x.Y)
	if tx == nil || ty == nil {
		return
	}
	switch {
	case types.IsInterface(tx) && !types.IsInterface(ty):
		s.boxType(tx, ty, x.Y, "comparison operand")
	case types.IsInterface(ty) && !types.IsInterface(tx):
		s.boxType(ty, tx, x.X, "comparison operand")
	}
}

// switchStmt: an expression switch compares the tag with each case
// expression as `==` (spec#Switch_statements), so an interface on either
// side boxes the other.
func (s *uintptrIdentityScan) switchStmt(x *ast.SwitchStmt) {
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
			if tc == nil {
				continue
			}
			switch {
			case types.IsInterface(tt) && !types.IsInterface(tc):
				s.boxType(tt, tc, ce, "switch case against an interface tag")
			case types.IsInterface(tc) && !types.IsInterface(tt):
				s.boxType(tc, tt, ce, "switch tag against an interface case")
			}
		}
	}
}

// rangeStmt: the ASSIGNMENT form (`for k, v = range x`) assigns the
// iteration values to existing variables (spec#For_range); the `:=` form
// declares them at the iteration types and converts nothing.
func (s *uintptrIdentityScan) rangeStmt(x *ast.RangeStmt) {
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
		return // range-over-func is FR-12's refusal
	}
	if x.Key != nil && !isBlankIdent(x.Key) {
		s.boxType(s.typeOf(x.Key), kt, x.Key, "range key assignment")
	}
	if x.Value != nil && !isBlankIdent(x.Value) {
		s.boxType(s.typeOf(x.Value), vt, x.Value, "range value assignment")
	}
}
