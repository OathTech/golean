// fmt call desugar — H-6, the Q3 OPTION 1 ruling (raft W4.1 item 2;
// docs/raft-w41-log.md item 2, docs/raft-w3-log.md §5).
//
// The modeled fmt surface is a SUBSET of Sprintf/Errorf/Fprintf over a
// CONSTANT format string and the measured verb x kind matrix, desugared
// AT EMIT TIME — never a runtime fmt model:
//
//   * the format string is parsed here; each verb pairs with its
//     argument's STATIC type and the pair must be in the modeled matrix
//     (below), else the call refuses per-declaration (fail closed);
//   * the call site becomes a call to a LIFTED per-site function
//     `<enclosing>$fmtN(a0, ..) string` whose body concatenates the
//     literal segments with per-verb helper calls over the parameters.
//     The lift is WHY argument evaluation order is exactly fmt's: all
//     arguments evaluate (left to right, at the call) BEFORE any
//     String()/Error() runs (probed against gc — order E1 E2 S1 S2 —
//     and pinned by fmt/sprintf-verbs/eval-order);
//   * the helpers are E5-injected Go source (stdlibshim.go,
//     goleanShimFmt*), lowered through the ordinary pipeline: digit
//     loops for %d/%x, the ASCII %q quoter, and the Stringer/error
//     renderers with fmt's recover-and-render behavior (verb char
//     without flags, "String method"/"Error method", the nil-pointer
//     "<nil>" and the nil-error "%!s(<nil>)"/"<nil>" forms — all
//     probed against gc, all pinned per-verb in fmt/sprintf-verbs);
//   * fmt.Errorf(...) = goleanShimErrorsNew(<the same lift>) — without
//     %w, fmt.Errorf IS errors.New over the text (fmt/errors.go), so
//     identity/nil-ness ride the E5 errors shim (co-injected);
//   * fmt.Fprintf(w, ...) is modeled ONLY for w of static type
//     *strings.Builder (the DescribeConfChange shape): it becomes
//     w.WriteString(<the lift>), whose results ((len, nil)) and
//     writer-then-args evaluation order equal Fprintf's.
//
// THE STRINGABLE-VERB RULE (audit A-F1 — the header used to state this
// backwards): gc's fmt consults error/Stringer for the verbs v, s, x,
// X, q (fmt/print.go handleMethods switches on exactly that set) and
// skips it ONLY for the pure-numeric verbs — %d and family — plus %T
// and %p. It is therefore %d-family, not "numeric verbs" in the loose
// sense, that renders an enum's NUMBER: %x over that same enum type
// would render the hex of its String() result. printArg's concrete-type
// fast switch never matches a NAMED type, so a defined uint64/[]byte
// with a String method always reaches handleMethods. The precedence
// check runs before the kind matrix below, for all four modeled
// stringable verbs.
//
// %X AND THE TWO-SITE INVARIANT (census G-11 residual, reconciled
// 2026-08-21 by gc probe): gc's set is {v,s,x,X,q} — probed at
// go1.26.5, `%X` over an Error-implementing uint64 prints the
// UPPERCASE hex of the method result ("OOPS" -> 4F4F5053), never the
// number — but `X` is OUTSIDE the modeled subset: parseFmtFormat
// refuses `%X` (the verb-set default arm), so the stringable switch
// below deliberately omits it. These two sites move together:
// admitting %X means adding it to the parser's verb set, to the
// stringable switch, AND an uppercase render arm in
// goleanShimFmtStringVerb — differential-pinned first, like every
// matrix widening.
//
// THE MODELED MATRIX (everything else refuses, naming the pair):
//
//   %d   signed / unsigned integer kinds (named included; enums are
//        named int32 — %d is the pure-numeric family, which skips the
//        Stringer check)
//   %x   error implementors; Stringer implementors (hex OF the method
//        result — probed: "HI!" -> 484921); else unsigned integer kinds
//        (lowercase hex of the number)
//   %s   error implementors; Stringer implementors; else string kinds
//   %v   error; Stringer; else integer kinds, string kinds, bool
//   %+v  exactly %v over this matrix (for these kinds the flag changes
//        nothing: Stringer/error take precedence, and the PANIC render
//        drops flags — probed: %!v, never %!+v)
//   %q   error implementors; Stringer implementors (the QUOTED method
//        result); else byte-slice kinds. ASCII subset either way — the
//        helper fails closed on bytes >= 0x80, where real %q prints
//        printable non-ASCII runes literally; recorded modeled-subset
//        bound. On a method result that bound is a PROPAGATING panic
//        (the post-process sits outside the render's recover frame), so
//        it stays fail-closed rather than becoming a PANIC render.
//   %%   a literal percent
//
// RECORDED BOUNDS (visible, never silent): a TYPED-NIL error boxed in
// a static `error` argument renders through Error()/the panic path
// where fmt's reflect-based nil check prints "<nil>" — undetectable
// without reflection at a static interface type; unreachable in the
// subject (its live error values come from constructors). For static
// POINTER types the nil check IS exact (computed in the lift from the
// pointer parameter). A String/Error method panicking with a
// non-string/non-error value, or panicking again inside the recovered
// render, propagates (fmt would nest-render); the plainpb stubs panic
// with string literals.

package main

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
)

// fmtDesugarFuncs is the modeled fmt surface. Consulted by the
// injection scan (stdlibshim.go) and by emitFmtCall.
var fmtDesugarFuncs = map[string]bool{
	"Sprintf": true,
	"Errorf":  true,
	"Fprintf": true,
}

// fmtStringerIface is fmt.Stringer's shape, constructed rather than
// injected: the desugar needs only the types.Implements answer.
var fmtStringerIface = func() *types.Interface {
	sig := types.NewSignatureType(nil, nil, nil, types.NewTuple(),
		types.NewTuple(types.NewVar(token.NoPos, nil, "", types.Typ[types.String])), false)
	iface := types.NewInterfaceType([]*types.Func{
		types.NewFunc(token.NoPos, nil, "String", sig)}, nil)
	iface.Complete()
	return iface
}()

// fmtVerb is one parsed conversion: the verb letter, the one modeled
// flag ('+' on v — recorded but semantically inert for the scalar
// matrix; it switches field names on for composites), and the one
// modeled width (digits before 'd' ONLY — the MajorityConfig.Describe
// `%5d`; space-pad left, sign inside, no truncation — gc-probed
// artifacts/w43/probe-fmt E1-E4).
type fmtVerb struct {
	verb  rune
	plus  bool
	width int
}

// parseFmtFormat splits a format string into literal segments and
// verbs: segs[0] verb[0] segs[1] verb[1] ... segs[n]. %% folds into
// the segments. Anything else — flags, width on a non-d verb,
// precision, argument indexes, unknown verbs — errors, naming the
// construct.
func parseFmtFormat(f string) ([]string, []fmtVerb, error) {
	segs := []string{}
	verbs := []fmtVerb{}
	cur := []byte{}
	for i := 0; i < len(f); i++ {
		c := f[i]
		if c != '%' {
			cur = append(cur, c)
			continue
		}
		if i+1 >= len(f) {
			return nil, nil, fmt.Errorf("format string ends in %%")
		}
		i++
		switch {
		case f[i] == '%':
			cur = append(cur, '%')
		case f[i] == 'd' || f[i] == 'x' || f[i] == 's' || f[i] == 'v' ||
			f[i] == 'q' || f[i] == 't':
			segs = append(segs, string(cur))
			cur = nil
			verbs = append(verbs, fmtVerb{verb: rune(f[i])})
		case f[i] >= '1' && f[i] <= '9':
			// Width digits: modeled for %d ONLY (the `%5d` shape).
			w := 0
			for i < len(f) && f[i] >= '0' && f[i] <= '9' {
				w = w*10 + int(f[i]-'0')
				i++
			}
			if i >= len(f) || f[i] != 'd' {
				return nil, nil, fmt.Errorf("width %d on verb %%%c is outside the modeled fmt subset (width is modeled for %%d only)", w, safeByte(f, i))
			}
			segs = append(segs, string(cur))
			cur = nil
			verbs = append(verbs, fmtVerb{verb: 'd', width: w})
		case f[i] == '+':
			if i+1 < len(f) && f[i+1] == 'v' {
				i++
				segs = append(segs, string(cur))
				cur = nil
				verbs = append(verbs, fmtVerb{verb: 'v', plus: true})
				break
			}
			return nil, nil, fmt.Errorf("verb %%+%c is outside the modeled fmt subset", safeByte(f, i+1))
		default:
			return nil, nil, fmt.Errorf("verb %%%c is outside the modeled fmt subset (modeled: %%d %%x %%s %%v %%+v %%q %%t %%%%)", f[i])
		}
	}
	segs = append(segs, string(cur))
	return segs, verbs, nil
}

func safeByte(s string, i int) byte {
	if i < len(s) {
		return s[i]
	}
	return '?'
}

// fmtArgPlan is one verb's compiled plan: the call-site argument nodes
// (evaluated once, in argument order), the lifted function's matching
// parameters, and the in-body expression rendering the verb over them.
type fmtArgPlan struct {
	callArgs []any
	params   []any
	body     any
}

// emitFmtCall is the H-6 hook: handled=true exactly for
// fmt.{Sprintf,Errorf,Fprintf} calls in the modeled subset; a call
// naming one of the three but falling outside the subset REFUSES here
// (never falls through to the package-selector refusal, which would
// misclassify a modeled-surface gap as an unmodeled package).
func (e *emitter) emitFmtCall(c *ast.CallExpr, sel *ast.SelectorExpr) (any, bool, error) {
	x, ok := sel.X.(*ast.Ident)
	if !ok {
		return nil, false, nil
	}
	pkgName, ok := e.info.Uses[x].(*types.PkgName)
	if !ok || pkgName.Imported().Path() != "fmt" || !fmtDesugarFuncs[sel.Sel.Name] {
		return nil, false, nil
	}
	fn := sel.Sel.Name
	if c.Ellipsis.IsValid() {
		return nil, false, unsup("fmt.%s with a spread argument (args...) is outside the modeled subset", fn)
	}
	formatIdx := 0
	if fn == "Fprintf" {
		formatIdx = 1
	}
	if len(c.Args) < formatIdx+1 {
		return nil, false, unsup("fmt.%s with no format string", fn)
	}

	// Fprintf's WRITER evaluates before the format arguments (fmt's own
	// argument order) — emit it first so its hoists land first.
	var recvNode any
	if fn == "Fprintf" {
		wTy := e.goTypeOf(c.Args[0])
		ptr, okPtr := types.Unalias(wTy).(*types.Pointer)
		if !okPtr || !isStringsBuilder(ptr.Elem()) {
			return nil, false, unsup("fmt.Fprintf writer of type %s is outside the modeled subset (modeled: *strings.Builder)", wTy)
		}
		var err error
		recvNode, err = e.emitExpr(c.Args[0])
		if err != nil {
			return nil, false, err
		}
	}

	tv, okTv := e.info.Types[c.Args[formatIdx]]
	if !okTv || tv.Value == nil || tv.Value.Kind() != constant.String {
		return nil, false, unsup("fmt.%s with a non-constant format string is outside the modeled subset (the verb/kind pairing is checked at emit time)", fn)
	}
	format := constant.StringVal(tv.Value)
	segs, verbs, perr := parseFmtFormat(format)
	if perr != nil {
		return nil, false, unsup("fmt.%s format %q: %v", fn, format, perr)
	}
	args := c.Args[formatIdx+1:]
	if len(args) != len(verbs) {
		return nil, false, unsup("fmt.%s format %q has %d verb(s) but %d argument(s) (fmt would render %%! markers; the modeled subset refuses instead)", fn, format, len(verbs), len(args))
	}

	// The lift body stays A-NORMAL: each helper CALL binds to a `$fK`
	// temp statement (in verb order — fmt formats left to right), and
	// the returned expression concatenates pure pieces only.
	strTy := map[string]any{"kind": "string"}
	callArgs := []any{}
	params := []any{}
	stmts := []any{}
	var concat any
	addPiece := func(node any) {
		if concat == nil {
			concat = node
			return
		}
		concat = map[string]any{"expr": "binary", "op": "+",
			"x": concat, "y": node, "operandType": strTy}
	}
	if segs[0] != "" || len(verbs) == 0 {
		addPiece(stringLitNode(segs[0]))
	}
	for k, v := range verbs {
		plan, err := e.fmtVerbArg(fn, format, v, args[k], k)
		if err != nil {
			return nil, false, err
		}
		callArgs = append(callArgs, plan.callArgs...)
		params = append(params, plan.params...)
		piece := plan.body
		if m, isMap := plan.body.(map[string]any); isMap && m["expr"] == "call" {
			tname := "$f" + itoa(k)
			stmts = append(stmts, map[string]any{
				"stmt": "assign", "define": true,
				"lhs": []any{map[string]any{"target": "declare", "id": tname, "type": strTy}},
				"rhs": []any{plan.body}})
			piece = map[string]any{"expr": "ident", "name": tname, "type": strTy}
		}
		addPiece(piece)
		if segs[k+1] != "" {
			addPiece(stringLitNode(segs[k+1]))
		}
	}

	var formatted any
	if len(verbs) == 0 {
		// No verb arguments: the result is the constant format text
		// (with %% folded); no lift is emitted.
		formatted = concat
	} else {
		liftName := e.curFuncName + "$fmt" + itoa(e.liftSeq)
		e.liftSeq++
		stmts = append(stmts, map[string]any{"stmt": "return", "results": []any{concat}})
		e.lifted = append(e.lifted, map[string]any{
			"name":     liftName,
			"params":   params,
			"results":  []any{map[string]any{"id": "$res0", "type": strTy}},
			"variadic": false,
			"body":     map[string]any{"stmt": "block", "body": stmts},
		})
		formatted = map[string]any{"expr": "call", "func": liftName,
			"args": callArgs, "resultTypes": []any{strTy}}
	}

	switch fn {
	case "Sprintf":
		return formatted, true, nil
	case "Errorf":
		// fmt.Errorf without %w IS errors.New over the formatted text
		// (%w is outside the parser's verb set, so it cannot arrive
		// here). The errors shim is co-injected with the fmt bundle
		// (stdlibshim.go) — a failed lookup is an internal
		// inconsistency, refused loudly.
		shimObj := e.pkg.Scope().Lookup(errorsNewShimName)
		shimFn, okShim := shimObj.(*types.Func)
		if !okShim {
			return nil, false, unsup("fmt.Errorf desugar: errors.New shim not injected (internal: the fmt bundle must co-inject it)")
		}
		inner := formatted
		if len(verbs) > 0 {
			// A call is not a pure expression (A-normal form): bind it
			// before nesting it as the constructor's argument.
			var err error
			inner, err = e.hoist(formatted, types.Typ[types.String])
			if err != nil {
				return nil, false, err
			}
		}
		errTy, err := e.emitType(types.Universe.Lookup("error").Type())
		if err != nil {
			return nil, false, err
		}
		return map[string]any{"expr": "call", "func": e.funcWireName(shimFn),
			"args": []any{inner}, "resultTypes": []any{errTy}}, true, nil
	case "Fprintf":
		inner := formatted
		if len(verbs) > 0 {
			var err error
			inner, err = e.hoist(formatted, types.Typ[types.String])
			if err != nil {
				return nil, false, err
			}
		}
		errTy, err := e.emitType(types.Universe.Lookup("error").Type())
		if err != nil {
			return nil, false, err
		}
		return map[string]any{"expr": "call", "func": "strings.Builder.WriteString",
			"args":        []any{recvNode, inner},
			"resultTypes": []any{intType("int"), errTy}}, true, nil
	}
	return nil, false, unsup("fmt.%s (internal: unreachable dispatch)", fn)
}

// isStringsBuilder reports whether t is the named type strings.Builder.
func isStringsBuilder(t types.Type) bool {
	n, ok := types.Unalias(t).(*types.Named)
	if !ok {
		return false
	}
	obj := n.Obj()
	return obj.Pkg() != nil && obj.Pkg().Path() == "strings" && obj.Name() == "Builder"
}

// fmtVerbArg compiles one verb x static-kind pair, or refuses naming
// it. Every call-site argument expression is emitted EXACTLY ONCE.
func (e *emitter) fmtVerbArg(fn, format string, v fmtVerb, arg ast.Expr, k int) (*fmtArgPlan, error) {
	strTy := map[string]any{"kind": "string"}
	argTy := e.goTypeOf(arg)
	verbName := "%" + string(v.verb)
	if v.plus {
		verbName = "%+v"
	}
	if v.width > 0 {
		verbName = "%" + itoa(v.width) + string(v.verb)
	}
	pname := "$a" + itoa(k)
	paramRef := func(ty any) map[string]any {
		return map[string]any{"expr": "ident", "name": pname, "type": ty}
	}
	helper := func(name string, hargs ...any) map[string]any {
		return map[string]any{"expr": "call", "func": e.fmtShimWireName(name),
			"args": hargs, "resultTypes": []any{strTy}}
	}
	// One converted scalar argument -> one parameter of the target type.
	scalar := func(target types.Type, helperName string) (*fmtArgPlan, error) {
		tw, err := e.emitType(target)
		if err != nil {
			return nil, err
		}
		node, err := e.emitExpr(arg)
		if err != nil {
			return nil, err
		}
		if !types.Identical(argTy, target) {
			node = map[string]any{"expr": "convert", "target": tw, "x": node}
		}
		body := any(paramRef(tw))
		if helperName != "" {
			body = helper(helperName, paramRef(tw))
		}
		return &fmtArgPlan{callArgs: []any{node}, params: []any{map[string]any{"id": pname, "type": tw}}, body: body}, nil
	}
	// A Stringer/error renderer over a CONCRETE static type: the call
	// passes the receiver's METHOD VALUE (func() string), captured at
	// the call site — the render helper invokes it under fmt's
	// recover-and-render. No interface dispatch exists anywhere on this
	// path (see fmtShimBundleKey's comment: chosen for fmt fidelity AND
	// reachability precision). For a static POINTER type the nil flag is
	// computed from the once-evaluated pointer (fmt's reflect nil check,
	// statically resolved); pointer-receiver methods imply a pointer
	// static type (Go's method sets), and a VALUE-receiver method
	// reached through a pointer argument is refused — capturing it would
	// deref at argument time where fmt derefs at render time, and the
	// nil-pointer behaviors differ (recorded; not in the census).
	render := func(methodName, helperLabel string) (*fmtArgPlan, error) {
		obj, index, _ := types.LookupFieldOrMethod(argTy, true, e.pkg, methodName)
		mfn, okFn := obj.(*types.Func)
		if !okFn || len(index) != 1 {
			return nil, unsup("fmt.%s verb %s: %s's %s method is promoted or missing (outside the modeled subset)", fn, verbName, argTy, methodName)
		}
		recvT := mfn.Type().(*types.Signature).Recv().Type()
		_, pointerRecv := recvT.(*types.Pointer)
		defType := recvT
		if ptr, isPtr := defType.(*types.Pointer); isPtr {
			defType = ptr.Elem()
		}
		typeName, okName := e.namedTypeName(defType)
		if !okName {
			return nil, unsup("fmt.%s verb %s: method on unnameable type %s", fn, verbName, argTy)
		}
		callSig := types.NewSignatureType(nil, nil, nil, types.NewTuple(),
			types.NewTuple(types.NewVar(token.NoPos, nil, "", types.Typ[types.String])), false)
		funcW, err := e.emitType(callSig)
		if err != nil {
			return nil, err
		}
		verbLit := stringLitNode(string(v.verb))
		methodLit := stringLitNode(helperLabel)
		node, err := e.emitExpr(arg)
		if err != nil {
			return nil, err
		}
		_, argIsPtr := types.Unalias(argTy).(*types.Pointer)
		if pointerRecv {
			if !argIsPtr {
				// Unreachable through go/types (a value type does not
				// implement via pointer-receiver methods) — refuse
				// rather than reason about it.
				return nil, unsup("fmt.%s verb %s: pointer-receiver %s on a non-pointer argument", fn, verbName, methodName)
			}
			ptrW, err := e.emitType(argTy)
			if err != nil {
				return nil, err
			}
			// Evaluate the pointer ONCE; both the nil flag and the
			// method value read the temp.
			tmp, err := e.hoist(node, argTy)
			if err != nil {
				return nil, err
			}
			nilCmp := map[string]any{"expr": "binary", "op": "==",
				"x": tmp, "y": map[string]any{"expr": "nil"}, "operandType": ptrW}
			mv := map[string]any{"expr": "func-value", "func": typeName + "." + methodName,
				"captured": []any{tmp}}
			nname := "$nil" + itoa(k)
			boolTyW := map[string]any{"kind": "bool"}
			return &fmtArgPlan{
				callArgs: []any{nilCmp, mv},
				params: []any{map[string]any{"id": nname, "type": boolTyW},
					map[string]any{"id": pname, "type": funcW}},
				body: helper("goleanShimFmtRender", verbLit, methodLit,
					map[string]any{"expr": "ident", "name": nname, "type": boolTyW},
					paramRef(funcW)),
			}, nil
		}
		if argIsPtr {
			return nil, unsup("fmt.%s verb %s: value-receiver %s reached through a pointer argument is outside the modeled subset (capture-time vs render-time deref)", fn, verbName, methodName)
		}
		mv := map[string]any{"expr": "func-value", "func": typeName + "." + methodName,
			"captured": []any{node}}
		return &fmtArgPlan{
			callArgs: []any{mv},
			params:   []any{map[string]any{"id": pname, "type": funcW}},
			body: helper("goleanShimFmtRender", verbLit, methodLit,
				map[string]any{"expr": "bool", "value": false}, paramRef(funcW)),
		}, nil
	}
	// A static-INTERFACE error argument (the raft shape: err values of
	// static type `error`): the goleanShimFmtError helper handles the
	// nil interface and calls Error() through the interface. The
	// dispatch edge this keeps is the `error.Error` anchor — every
	// concrete Error method in the program is a reachability candidate
	// through it, and every one in the subject tree LOWERS (they are
	// one-line text returns), so it costs the census nothing (checked
	// by the post-item sweep).
	renderErrIface := func() (*fmtArgPlan, error) {
		errT := types.Universe.Lookup("error").Type()
		targetW, err := e.emitType(errT)
		if err != nil {
			return nil, err
		}
		node, err := e.emitExpr(arg)
		if err != nil {
			return nil, err
		}
		boxed, err := e.wrapInterfaceConversion(errT, argTy, node)
		if err != nil {
			return nil, err
		}
		return &fmtArgPlan{
			callArgs: []any{boxed},
			params:   []any{map[string]any{"id": pname, "type": targetW}},
			body: helper("goleanShimFmtError", stringLitNode(string(v.verb)),
				paramRef(targetW)),
		}, nil
	}

	basic, _ := argTy.Underlying().(*types.Basic)
	errIface := types.Universe.Lookup("error").Type().Underlying().(*types.Interface)
	implementsError := types.Implements(argTy, errIface)
	implementsStringer := types.Implements(argTy, fmtStringerIface)

	// THE STRINGABLE-VERB PRECEDENCE, FIRST (audit A-F1). gc's fmt
	// consults error/Stringer for v, s, x, X, q — fmt/print.go
	// handleMethods switches on exactly that set — and skips it only
	// for the pure-numeric verbs (%d and family) and %T/%p. A named
	// type never matches printArg's concrete-type fast switch, so a
	// Stringer-implementing uint64 reaches handleMethods and %x prints
	// the hex OF THE String() RESULT, not of the number (probed: "HI!"
	// -> 484921). Putting this ahead of the kind matrix is what keeps
	// %x/%q honest; the render helpers post-process the method result
	// by verb (goleanShimFmtStringVerb).
	switch v.verb {
	// No 'X' here BY PAIRING with the parser, not by oversight: gc
	// consults error/Stringer for %X too (uppercase hex of the method
	// result, probed 2026-08-21), but parseFmtFormat refuses %X, so it
	// cannot arrive. If the parser ever admits it, this case list and
	// the render helper gain it in the same change (header: "%X AND
	// THE TWO-SITE INVARIANT").
	case 's', 'v', 'x', 'q':
		if implementsError {
			if types.IsInterface(argTy) {
				return renderErrIface()
			}
			return render("Error", "Error")
		}
		if implementsStringer {
			if types.IsInterface(argTy) {
				return nil, unsup("fmt.%s verb %s over a non-error interface type %s is outside the modeled subset", fn, verbName, argTy)
			}
			return render("String", "String")
		}
	}

	// One converted scalar argument rendered through a helper taking an
	// extra WIDTH argument (the %5d family): same shape as scalar(), the
	// width traveling as an int literal.
	scalarPad := func(target types.Type, helperName string, width int) (*fmtArgPlan, error) {
		tw, err := e.emitType(target)
		if err != nil {
			return nil, err
		}
		node, err := e.emitExpr(arg)
		if err != nil {
			return nil, err
		}
		if !types.Identical(argTy, target) {
			node = map[string]any{"expr": "convert", "target": tw, "x": node}
		}
		widthLit := map[string]any{"expr": "int", "value": itoa(width),
			"type": map[string]any{"kind": "int", "int": "int"}}
		return &fmtArgPlan{callArgs: []any{node},
			params: []any{map[string]any{"id": pname, "type": tw}},
			body:   helper(helperName, paramRef(tw), widthLit)}, nil
	}

	switch v.verb {
	case 'd':
		if basic != nil && basic.Info()&types.IsInteger != 0 {
			if v.width > 0 {
				if basic.Info()&types.IsUnsigned != 0 {
					return scalarPad(types.Typ[types.Uint64], "goleanShimFmtUintPad", v.width)
				}
				return scalarPad(types.Typ[types.Int64], "goleanShimFmtIntPad", v.width)
			}
			if basic.Info()&types.IsUnsigned != 0 {
				return scalar(types.Typ[types.Uint64], "goleanShimFmtUint")
			}
			return scalar(types.Typ[types.Int64], "goleanShimFmtInt")
		}
	case 't':
		if basic != nil && basic.Info()&types.IsBoolean != 0 {
			return scalar(types.Typ[types.Bool], "goleanShimFmtBool")
		}
	case 'x':
		if basic != nil && basic.Info()&types.IsInteger != 0 && basic.Info()&types.IsUnsigned != 0 {
			return scalar(types.Typ[types.Uint64], "goleanShimFmtHex")
		}
	case 's', 'v':
		if basic != nil && basic.Info()&types.IsString != 0 {
			return scalar(types.Typ[types.String], "")
		}
		if v.verb == 'v' {
			if basic != nil && basic.Info()&types.IsInteger != 0 {
				if basic.Info()&types.IsUnsigned != 0 {
					return scalar(types.Typ[types.Uint64], "goleanShimFmtUint")
				}
				return scalar(types.Typ[types.Int64], "goleanShimFmtInt")
			}
			if basic != nil && basic.Info()&types.IsBoolean != 0 {
				return scalar(types.Typ[types.Bool], "goleanShimFmtBool")
			}
		}
	case 'q':
		if isByteSlice(argTy.Underlying()) {
			return scalar(types.NewSlice(types.Typ[types.Byte]), "goleanShimFmtQuoteBytes")
		}
		if basic != nil && basic.Info()&types.IsString != 0 {
			// The StateType.MarshalJSON shape (%q over st.String()'s
			// result). Same ASCII bound as the byte-slice cell.
			return scalar(types.Typ[types.String], "goleanShimFmtQuoteString")
		}
	}
	// %v/%+v over a modeled COMPOSITE static type (slices, named structs,
	// recursively — fmtcomposite.go). Tried after the scalar matrix so a
	// scalar cell never re-routes; handled=false falls to the refusal.
	if v.verb == 'v' {
		plan, handled, err := e.fmtCompositeArg(fn, v, arg, k)
		if handled || err != nil {
			return plan, err
		}
	}
	return nil, unsup("fmt.%s verb %s over an argument of type %s is outside the modeled verb/kind matrix (format %q; fail closed — widen with a differential pin first)", fn, verbName, argTy, format)
}

// fmtShimWireName mints the FuncId of an injected fmt helper in the
// CURRENT unit (bare in main, path-qualified in a local unit — the E5
// discipline). The injection scan guarantees presence; a miss emits a
// dangling name the decoder refuses (never silent).
func (e *emitter) fmtShimWireName(name string) string {
	if fn, ok := e.pkg.Scope().Lookup(name).(*types.Func); ok {
		return e.funcWireName(fn)
	}
	return name
}

// ---- package-variable method desugars (H-14, raft W4.1 item 4) ----

// binaryVarMethodShims: import path -> exported package VARIABLE ->
// method -> injected shim name. The call `binary.LittleEndian.Uint64(x)`
// is a METHOD on a package variable of an UNEXPORTED type, which the
// plain E5 selector path cannot name; the desugar rewrites exactly the
// modeled members to their shims, and every other member of a LISTED
// variable refuses HERE with a message naming the member (never the
// old anonymous-type resolution error).
var binaryVarMethodShims = map[string]map[string]map[string]string{
	"encoding/binary": {
		"LittleEndian": {
			"Uint64":    binaryLEUint64ShimName,
			"PutUint64": binaryLEPutUint64ShimName,
		},
	},
}

// emitBinaryVarMethodCall is the H-14 hook: handled=true exactly for
// modeled `pkg.Var.Method(args)` shapes; a LISTED variable's unmodeled
// member refuses; everything else falls through untouched.
func (e *emitter) emitBinaryVarMethodCall(c *ast.CallExpr, sel *ast.SelectorExpr) (any, bool, error) {
	sel2, ok := sel.X.(*ast.SelectorExpr)
	if !ok {
		return nil, false, nil
	}
	x2, ok := sel2.X.(*ast.Ident)
	if !ok {
		return nil, false, nil
	}
	pkgName, ok := e.info.Uses[x2].(*types.PkgName)
	if !ok {
		return nil, false, nil
	}
	vars, ok := binaryVarMethodShims[pkgName.Imported().Path()]
	if !ok {
		return nil, false, nil
	}
	methods, ok := vars[sel2.Sel.Name]
	if !ok {
		return nil, false, nil
	}
	shimName, ok := methods[sel.Sel.Name]
	if !ok {
		return nil, false, unsup("%s.%s.%s is outside the modeled subset (modeled members: Uint64, PutUint64 — widen with a differential pin first)",
			pkgName.Imported().Path(), sel2.Sel.Name, sel.Sel.Name)
	}
	fn, ok := e.info.Uses[sel.Sel].(*types.Func)
	if !ok {
		return nil, false, unsup("%s.%s.%s did not resolve to a method",
			pkgName.Imported().Path(), sel2.Sel.Name, sel.Sel.Name)
	}
	sig, ok := fn.Type().(*types.Signature)
	if !ok {
		return nil, false, unsup("%s.%s.%s has no signature",
			pkgName.Imported().Path(), sel2.Sel.Name, sel.Sel.Name)
	}
	shimObj := e.pkg.Scope().Lookup(shimName)
	shimFn, ok := shimObj.(*types.Func)
	if !ok {
		return nil, false, unsup("shim %s not injected for %s.%s.%s",
			shimName, pkgName.Imported().Path(), sel2.Sel.Name, sel.Sel.Name)
	}
	args, err := e.emitCallArgs(sig, c)
	if err != nil {
		return nil, false, err
	}
	resultTypes, err := e.emitResultTypes(sig)
	if err != nil {
		return nil, false, err
	}
	return map[string]any{"expr": "call", "func": e.funcWireName(shimFn),
		"args": args, "resultTypes": resultTypes}, true, nil
}
