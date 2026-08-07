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
	"sort"
	"strings"
)

// ---- program ----

func (e *emitter) emitProgram(files []*ast.File) (map[string]any, error) {
	funcs := []any{}
	methods := []any{}
	typeDefs := []any{}

	// Package-level variables first (init slice): gids assigned here are
	// what every `globaladdr` in the emitted bodies refers to.
	if err := e.collectGlobals(files); err != nil {
		return nil, err
	}

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
				// init() functions (init slice): exported under reserved
				// mangled ids `$initN` (source order, files in lexical
				// filename order — the spec's presentation order), called
				// by the synthesized $pkginit after the variable
				// initializers. go/types enforces the declaration rules
				// (no params/results, not callable, not referenceable).
				// NO per-decl quarantine: init runs before every subject,
				// so an unsupported init body refuses the whole export
				// (design note §2).
				if d.Recv == nil && d.Name.Name == "init" {
					mangled := "$init" + itoa(len(e.initFuncNames))
					e.initFuncNames = append(e.initFuncNames, mangled)
					e.curFuncName = mangled
					e.liftSeq = 0
					fn, err := e.emitFuncDecl(d)
					if err != nil {
						return nil, err
					}
					fn["name"] = mangled
					funcs = append(funcs, e.lifted...)
					e.lifted = nil
					funcs = append(funcs, fn)
					continue
				}
				// Generic declarations are never emitted uninstantiated
				// (spec: a generic function/type must be instantiated
				// before use — no runtime artifact exists for the
				// uninstantiated form). Function stencils are emitted from
				// the instantiation worklist (mono.go); generic METHODS
				// stencil with their receiver instantiation (G3).
				if fsig, isSig := e.info.Defs[d.Name].Type().(*types.Signature); isSig {
					if fsig.TypeParams().Len() > 0 {
						if fnObj, isFn := e.info.Defs[d.Name].(*types.Func); isFn {
							if e.genericFuncDecls == nil {
								e.genericFuncDecls = map[*types.Func]*ast.FuncDecl{}
							}
							e.genericFuncDecls[fnObj] = d
						}
						continue
					}
					if fsig.RecvTypeParams().Len() > 0 {
						// Method on a generic type: stenciled per receiver
						// instantiation (G3); uses of the instantiated
						// type fail closed until then.
						e.recordGenericMethod(d)
						continue
					}
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
					if rn, ok := e.namedTypeName(rt); ok {
						e.curFuncName = rn + "." + d.Name.Name
					}
				}
				e.liftSeq = 0
				localTypesMark := len(e.localTypeDefs)
				localIfaceMark := len(e.localIfaceMethods)
				namedStructMark := len(e.namedStructTypes)
				// The $deferRecoverNoop registration rides e.lifted, so it
				// must roll back WITH it (BUG-031: a sticky flag left later
				// `defer recover()`s referencing a never-emitted function).
				deferNoopMark := e.deferNoopEmitted
				monoMark := e.markMono()
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
						e.deferNoopEmitted = deferNoopMark
						// Drop any local type defs the quarantined body
						// half-registered (a leak could spuriously collide
						// with another function's local type).
						e.localTypeDefs = e.localTypeDefs[:localTypesMark]
						e.localIfaceMethods = e.localIfaceMethods[:localIfaceMark]
						// A wrapper for a rolled-back local type would
						// reference a TypeDef that never ships.
						e.namedStructTypes = e.namedStructTypes[:namedStructMark]
						// Instantiations the refused body registered roll
						// back too (audit response m5): a surviving TYPE
						// stencil has no quarantine of its own and would
						// refuse the WHOLE export from a body that was
						// already stubbed out (pinned by
						// generics/quarantined-instantiation).
						e.rollbackMono(monoMark)
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
				tds, ims, err := e.emitGenDeclTypes(d)
				if err != nil {
					return nil, err
				}
				typeDefs = append(typeDefs, tds...)
				methods = append(methods, ims...)
			}
		}
	}

	// The synthesized $pkginit (init slice): variable initializers in
	// go/types' InitOrder, then the $initN calls. After the FuncDecl loop
	// so initFuncNames is complete; its lifted literals flush like any
	// other function's.
	pkginit, err := e.synthesizePkgInit()
	if err != nil {
		return nil, err
	}
	if pkginit != nil {
		funcs = append(funcs, e.lifted...)
		e.lifted = nil
		funcs = append(funcs, pkginit)
	}

	// Drain the instantiation worklists (mono.go): function stencils for
	// every generic-function instantiation reachable from the emitted
	// bodies (subjects, helpers, $pkginit), plus TypeDef/method stencils
	// for every instantiated type that reached the wire — including
	// derived instantiations registered DURING stenciling, to a joint
	// fixpoint. Unsupported FUNCTION stencils quarantine into fail-closed
	// stubs exactly like unsupported plain declarations; type and method
	// stencils follow the standing whole-export policy.
	funcs, typeDefs, methods, err = e.drainMono(funcs, typeDefs, methods)
	if err != nil {
		return nil, err
	}

	// Promotion wrappers (design note 2026-08-05 D1.3): one synthesized
	// forwarding method per PROMOTED method-set entry of every declared
	// named struct type, so the machine's flat method table is COMPLETE
	// (the D2 wire contract). Runs BEFORE the interface-anchor pass below:
	// a wrapper forwarding to an embedded interface field records its
	// dispatch target in calledIfaceMethods.
	wrappers, err := e.synthesizePromotionWrappers()
	if err != nil {
		return nil, err
	}
	methods = append(methods, wrappers...)
	// Wrapper signatures can mention instantiated types: drain again.
	// (An instantiated STRUCT first appearing here would miss its own
	// wrapper pass. CORRECTED, arc-final audit F13 2026-08-06: the old
	// claim that this "can only make a promoted method visibly MISSING,
	// never silently wrong" was unsound — under D2 a missing wrapper
	// entry makes firstUnsatisfiedMethod? answer a definite FALSE, and a
	// comma-ok assert turns that into a silently wrong boolean, exactly
	// BUG-007's recorded finding-5 mode (verified by wire surgery on
	// promoted-method-assert-ok). No REACHABLE instance is known: every
	// type a wrapper's substituted signature can mention is also
	// mentioned by the corresponding method stencil, which the FIRST
	// drain's fixpoint flushes, and imported generic instantiation is
	// refused. If late-registered structs ever become reachable here,
	// the wrapper pass must move inside the drain fixpoint — do not
	// lean on the old safety claim.)
	funcs, typeDefs, methods, err = e.drainMono(funcs, typeDefs, methods)
	if err != nil {
		return nil, err
	}

	// Interface-dispatch anchors for interfaces NOT declared in this package
	// (predeclared error; imported interfaces later): every emitted
	// "<Iface>.<Method>" call needs a table entry, but only package-declared
	// interfaces got one above. Synthesize the missing ones from the recorded
	// calls, in sorted order for a deterministic wire.
	declaredIface := map[string]bool{}
	for _, m := range methods {
		if mm, ok := m.(map[string]any); ok && mm["interface"] == true {
			declaredIface[mm["recvType"].(string)+"."+mm["name"].(string)] = true
		}
	}
	calledKeys := make([]string, 0, len(e.calledIfaceMethods))
	for k := range e.calledIfaceMethods {
		calledKeys = append(calledKeys, k)
	}
	sort.Strings(calledKeys)
	for _, k := range calledKeys {
		if declaredIface[k] {
			continue
		}
		var resultsW []any
		cm := e.calledIfaceMethods[k]
		// Emit the anchor signature under the CALL SITE's stencil
		// substitution (arc-final audit F5): the key is
		// substitution-aware, the recorded origin sig is not.
		savedSubst, savedName, savedErr := e.curSubst, e.curFuncName, e.substErr
		savedTargs := e.curTargs
		e.curSubst, e.curFuncName, e.substErr = cm.subst, k, nil
		e.curTargs = nil
		params, err := e.emitParams(cm.sig.Params())
		if err == nil {
			var rerr error
			if resultsW, rerr = e.emitResults(cm.sig.Results()); rerr != nil {
				err = rerr
			}
		}
		e.curSubst, e.curFuncName, e.substErr = savedSubst, savedName, savedErr
		e.curTargs = savedTargs
		if err != nil {
			return nil, err
		}
		results := resultsW
		methods = append(methods, map[string]any{
			"name":      cm.method,
			"recvType":  cm.ifaceName,
			"recv":      map[string]any{"id": "$recv", "type": map[string]any{"kind": "interface", "name": cm.ifaceName}},
			"params":    params,
			"results":   results,
			"variadic":  cm.sig.Variadic(),
			"interface": true,
		})
	}

	// Imported-type method-set declarations (design note D5, BUG-009's
	// satisfaction polarity): marker TypeDefs + signature stubs. BEFORE
	// the interface-declaration pass — a stub signature can mention a
	// fresh interface.
	importedDefs, importedStubs := e.importedTypeDecls()
	typeDefs = append(typeDefs, importedDefs...)
	methods = append(methods, importedStubs...)

	// Interface DECLARATIONS: one `interface` TypeDef per interface type that
	// reached the wire anywhere (declared here, predeclared `error`, or
	// imported), carrying the FULL method set — embedded interfaces included,
	// since *types.Interface.NumMethods/Method is the complete set. This is
	// the machine's satisfaction requirement list, and its ABSENCE is what
	// makes an unknown interface fail closed instead of being vacuously
	// satisfied (pre-merge audit 2026-07-31, finding 0). Sorted for a
	// deterministic wire; the canonical empty interface `any` is excluded
	// (satisfied by design).
	// A method signature can itself mention a fresh interface, so this runs to
	// a FIXPOINT over the seen set rather than one pass.
	// Instantiated types can surface inside interface method signatures
	// and vice versa, so the fixpoint interleaves the mono drain.
	ifaceDefs := map[string]any{}
	for {
		funcs, typeDefs, methods, err = e.drainMono(funcs, typeDefs, methods)
		if err != nil {
			return nil, err
		}
		pending := []string{}
		for k := range e.seenInterfaces {
			if _, done := ifaceDefs[k]; !done {
				pending = append(pending, k)
			}
		}
		if len(pending) == 0 {
			break
		}
		sort.Strings(pending)
		for _, name := range pending {
			iface := e.seenInterfaces[name]
			sigs := []any{}
			for i := 0; i < iface.NumMethods(); i++ {
				m := iface.Method(i)
				sig := m.Type().(*types.Signature)
				params, err := e.emitTupleTypes(sig.Params())
				if err != nil {
					return nil, err
				}
				results, err := e.emitTupleTypes(sig.Results())
				if err != nil {
					return nil, err
				}
				// `variadic` is part of the SIGNATURE Go compares for
				// method-set membership: `M(xs ...int)` and `M(xs []int)`
				// are different methods (pre-merge audit 2026-07-31,
				// finding 0). Carried on both sides — here for the
				// requirement, on the `Func` for the implementation.
				sigs = append(sigs, map[string]any{
					"name": m.Name(), "params": params, "results": results,
					"variadic": sig.Variadic()})
			}
			ifaceDefs[name] = map[string]any{"kind": "interface", "methods": sigs}
		}
	}
	ifaceNames := make([]string, 0, len(ifaceDefs))
	for k := range ifaceDefs {
		ifaceNames = append(ifaceNames, k)
	}
	sort.Strings(ifaceNames)
	for _, name := range ifaceNames {
		typeDefs = append(typeDefs, map[string]any{"name": name, "def": ifaceDefs[name]})
	}

	// Function-local type declarations, registered during body emission
	// (emitDeclStmt, including stenciled bodies — hence appended after the
	// LAST mono drain): they join the global table — Go type declarations
	// have no runtime effect — with the duplicate-TypeId refusal below
	// guarding collisions.
	typeDefs = append(typeDefs, e.localTypeDefs...)
	methods = append(methods, e.localIfaceMethods...)

	// The TypeId keys are built; refuse the export if two import paths
	// collided on one package-name qualifier (findings 4/7).
	if err := e.checkPackageNameCollisions(); err != nil {
		return nil, err
	}
	// Duplicate TypeIds (e.g. two functions each declaring a local
	// `type T int`, or a local type shadowing a package-level one) would
	// silently alias in GoCore's global type table — refuse.
	seenTypeIds := map[string]bool{}
	for _, td := range typeDefs {
		if m, ok := td.(map[string]any); ok {
			if n, ok := m["name"].(string); ok {
				if seenTypeIds[n] {
					return nil, unsup("duplicate TypeId %s (a function-local type collides with another declaration)", n)
				}
				seenTypeIds[n] = true
			}
		}
	}

	// Transitive quarantine check (audit response 2026-08-05, C3): if
	// $pkginit's CALL GRAPH reaches a per-decl-quarantined function, the
	// whole export refuses — the same rule as a directly-unsupported
	// initializer, extended transitively. Without this, $pkginit hit the
	// stub at RUNTIME, poisoning every subject in the package with a
	// runtime-shaped refusal instead of the export-time one (the shape is
	// raft-real: `var ErrX = errors.New(...)` calling into a quarantined
	// helper). Runs after wrappers/stubs so the name->body map is complete.
	if err := checkInitQuarantine(funcs, methods); err != nil {
		return nil, err
	}

	program := map[string]any{
		"schema":  "golean-native-v1",
		"package": e.pkg.Name(),
		"types":   typeDefs,
		"funcs":   funcs,
		"methods": methods,
	}
	// Only when the package has package-level variables — a globals-free
	// wire stays byte-identical to before the init slice.
	if len(e.globalDefs) > 0 {
		program["globals"] = e.globalDefs
	}
	return program, nil
}

// ---- package initialization (init slice, docs/2026-08-05_init-design.md) ----

// collectGlobals assigns every package-level variable its dense gid in
// declaration order (files already in lexical filename order) and builds
// the wire globals table plus the fabricated per-initializer assignment
// statements $pkginit emission reuses. The SINGLE gid source: the driver
// seeds cell gid at Loc.base(gid) in the same order. An unsupported
// global TYPE refuses the whole export — initialization must zero-seed
// every global before any subject runs, so there is no per-decl
// quarantine for init code (design note §2).
func (e *emitter) collectGlobals(files []*ast.File) error {
	e.globalVars = map[*types.Var]int{}
	e.globalInitStmt = map[ast.Expr]*ast.AssignStmt{}
	for _, f := range files {
		for _, decl := range f.Decls {
			gd, ok := decl.(*ast.GenDecl)
			if !ok || gd.Tok != token.VAR {
				continue
			}
			for _, spec := range gd.Specs {
				vs, ok := spec.(*ast.ValueSpec)
				if !ok {
					continue
				}
				for i, name := range vs.Names {
					if name.Name != "_" {
						obj, isVar := e.info.Defs[name].(*types.Var)
						if !isVar || obj == nil {
							return unsup("package-level variable %s has no type object", name.Name)
						}
						ty, err := e.emitType(obj.Type())
						if err != nil {
							return err
						}
						e.globalVars[obj] = len(e.globalDefs)
						e.globalDefs = append(e.globalDefs, map[string]any{
							"name": name.Name, "type": ty})
					}
					// Fabricated assignment per initializer value, keyed by
					// the RHS expression (pointer identity — types.Initializer
					// carries the same node): Lhs are the ORIGINAL declaring
					// idents, so emitAssign's machinery (hoists, interface
					// boxing, blank targets, multi-value calls) applies
					// unchanged. One n:n spec fabricates per-pair; a
					// multi-value spec fabricates once with every name.
					switch {
					case len(vs.Values) == len(vs.Names) && i < len(vs.Values):
						e.globalInitStmt[vs.Values[i]] = &ast.AssignStmt{
							Lhs: []ast.Expr{name}, Tok: token.ASSIGN,
							Rhs: []ast.Expr{vs.Values[i]}}
					case len(vs.Values) == 1 && len(vs.Names) > 1 && i == 0:
						lhs := make([]ast.Expr, len(vs.Names))
						for j, n := range vs.Names {
							lhs[j] = n
						}
						e.globalInitStmt[vs.Values[0]] = &ast.AssignStmt{
							Lhs: lhs, Tok: token.ASSIGN,
							Rhs: []ast.Expr{vs.Values[0]}}
					}
				}
			}
		}
	}
	return nil
}

// collectCalledFuncs walks a wire subtree recording every function NAME it
// references — "func" is the one key carrying callee/func-value identities
// (call, func-value, method-call nodes). Conservative on purpose: a
// func-value merely STORED during init counts as reachable even if init
// never invokes it (the lexical-dependency-rule analog; recorded in the
// design note §2).
func collectCalledFuncs(node any, out map[string]bool) {
	switch n := node.(type) {
	case map[string]any:
		if fn, ok := n["func"].(string); ok {
			out[fn] = true
		}
		for _, v := range n {
			collectCalledFuncs(v, out)
		}
	case []any:
		for _, v := range n {
			collectCalledFuncs(v, out)
		}
	}
}

// checkInitQuarantine refuses the export when $pkginit's call graph
// (transitively, through emitted function and method bodies) reaches a
// quarantined declaration (audit response 2026-08-05, C3). This is full
// STATIC reachability — a quarantined function on a branch init never
// takes at runtime still refuses the export (deliberate over-closure,
// recorded in the design note). An interface-dispatch anchor `I.M` in
// the graph (a bodyless method-table entry) expands conservatively to
// EVERY emitted concrete method named `M`, whatever its receiver
// (delta-review M1, 2026-08-05: the BFS previously stored the anchor's
// nil body and never visited any implementation, so an
// interface-dispatched initializer reaching a quarantined function
// exported cleanly and poisoned every subject at runtime).
func checkInitQuarantine(funcs, methods []any) error {
	bodies := map[string]any{}
	quarantined := map[string]string{}
	// Interface dispatch anchors: "I.M" -> method name M; and per method
	// NAME, every CONCRETE method-table key ("T.M"), body-bearing or
	// quarantined-stub, an anchor expands to.
	anchors := map[string]string{}
	methodKeysByName := map[string][]string{}
	record := func(key string, m map[string]any) {
		if reason, ok := m["unsupported"].(string); ok {
			quarantined[key] = reason
			return
		}
		bodies[key] = m["body"]
	}
	for _, f := range funcs {
		if m, ok := f.(map[string]any); ok {
			if name, ok := m["name"].(string); ok {
				record(name, m)
			}
		}
	}
	for _, f := range methods {
		if m, ok := f.(map[string]any); ok {
			name, _ := m["name"].(string)
			rt, _ := m["recvType"].(string)
			if name == "" || rt == "" {
				continue
			}
			key := rt + "." + name
			if isIface, _ := m["interface"].(bool); isIface {
				anchors[key] = name
				continue
			}
			methodKeysByName[name] = append(methodKeysByName[name], key)
			record(key, m)
		}
	}
	start, ok := bodies["$pkginit"]
	if !ok {
		return nil
	}
	seen := map[string]bool{"$pkginit": true}
	frontier := []any{start}
	for len(frontier) > 0 {
		node := frontier[0]
		frontier = frontier[1:]
		called := map[string]bool{}
		collectCalledFuncs(node, called)
		names := make([]string, 0, len(called))
		for name := range called {
			names = append(names, name)
		}
		sort.Strings(names) // deterministic refusal message
		for _, name := range names {
			if reason, bad := quarantined[name]; bad {
				return unsup("package initialization reaches quarantined function %s (%s)", name, reason)
			}
			if mname, isAnchor := anchors[name]; isAnchor {
				// Conservative dispatch expansion: every concrete method
				// with the anchor's name is a candidate implementation.
				for _, key := range methodKeysByName[mname] {
					if reason, bad := quarantined[key]; bad {
						return unsup("package initialization reaches quarantined method %s via interface dispatch %s (%s)", key, name, reason)
					}
					if !seen[key] {
						seen[key] = true
						if b, ok := bodies[key]; ok {
							frontier = append(frontier, b)
						}
					}
				}
				continue
			}
			if !seen[name] {
				seen[name] = true
				if b, ok := bodies[name]; ok {
					frontier = append(frontier, b)
				}
			}
		}
	}
	return nil
}

// globalAddr returns the wire address node for a package-level variable,
// when it has a seeded cell.
func (e *emitter) globalAddr(v *types.Var) (any, bool) {
	gid, ok := e.globalVars[v]
	if !ok {
		return nil, false
	}
	return map[string]any{"expr": "globaladdr", "gid": gid}, true
}

// isPackageVar classifies an object as a package-level variable of THIS
// package (the frontend's static half of global resolution; go/types did
// the name resolution).
func (e *emitter) isPackageVar(obj types.Object) (*types.Var, bool) {
	v, isVar := obj.(*types.Var)
	if !isVar || v == nil || v.Parent() != e.pkg.Scope() {
		return nil, false
	}
	return v, true
}

// synthesizePkgInit builds the reserved $pkginit function: the package's
// variable initializers in go/types' InitOrder (the spec's stepwise
// dependency order — trust surface argument in the design note §1), then
// the init() functions in source order. Returns nil when the package has
// neither. Failures refuse the whole export (no per-decl quarantine for
// init code).
func (e *emitter) synthesizePkgInit() (map[string]any, error) {
	if len(e.info.InitOrder) == 0 && len(e.initFuncNames) == 0 {
		return nil, nil
	}
	e.curFuncName = "$pkginit"
	e.liftSeq = 0
	e.curResults = nil
	stmts := make([]ast.Stmt, 0, len(e.info.InitOrder))
	e.fnHasRecv = false
	for _, ini := range e.info.InitOrder {
		as, ok := e.globalInitStmt[ini.Rhs]
		if !ok {
			return nil, unsup("package-level initializer with no declaration site")
		}
		if containsRecv(as) {
			e.fnHasRecv = true
		}
		stmts = append(stmts, as)
	}
	body, err := e.emitStmtList(stmts)
	if err != nil {
		return nil, err
	}
	for _, name := range e.initFuncNames {
		body = append(body, map[string]any{"stmt": "expr", "expr": map[string]any{
			"expr": "call", "func": name, "args": []any{}, "resultTypes": []any{}}})
	}
	return map[string]any{
		"name":     "$pkginit",
		"params":   []any{},
		"results":  []any{},
		"variadic": false,
		"body":     map[string]any{"stmt": "block", "body": body},
	}, nil
}

// emitTupleTypes emits just the TYPES of a signature tuple (no parameter
// names): the shape an interface method REQUIREMENT compares against.
func (e *emitter) emitTupleTypes(t *types.Tuple) ([]any, error) {
	out := []any{}
	for i := 0; i < t.Len(); i++ {
		ty, err := e.emitType(t.At(i).Type())
		if err != nil {
			return nil, err
		}
		out = append(out, ty)
	}
	return out, nil
}

// emitGenDeclTypes emits type declarations (only defined struct types carry a
// GoCore TypeDef today; defined types over primitives/maps/arrays are handled
// by their use-site types, and their methods by the method table). Interface
// type declarations emit no TypeDef but contribute one bodyless entry per
// method of their FULL method set (embedded interfaces included) to the
// program METHODS list — the dispatch table the interfaces campaign's
// "<InterfaceName>.<Method>" calls resolve through.
func (e *emitter) emitGenDeclTypes(d *ast.GenDecl) ([]any, []any, error) {
	if d.Tok != token.TYPE {
		return nil, nil, nil
	}
	ifaceMethods := []any{}
	out := []any{}
	for _, spec := range d.Specs {
		ts := spec.(*ast.TypeSpec)
		obj := e.info.Defs[ts.Name]
		named, ok := obj.Type().(*types.Named)
		if !ok {
			continue
		}
		// GENERIC type declarations emit nothing here: they cannot be
		// used uninstantiated (spec §Type definitions), and each
		// instantiation gets its own TypeDef under its mangled TypeId
		// from the monomorphization worklist (mono.go; uses fail closed
		// until that stage lands).
		if named.TypeParams().Len() > 0 {
			continue
		}
		qname := e.qualifiedTypeName(named.Obj())
		if st, isStruct := named.Underlying().(*types.Struct); isStruct {
			fields := []any{}
			for i := 0; i < st.NumFields(); i++ {
				fld := st.Field(i)
				fty, err := e.emitType(fld.Type())
				if err != nil {
					return nil, nil, err
				}
				// `embedded` records Go's ANONYMOUS field flag verbatim —
				// honest struct-shape information (it is part of struct
				// identity for conversions). The machine no longer needs it
				// for satisfaction: promotion is flattened at emission and
				// the method table is complete (design note 2026-08-05 D2).
				fields = append(fields, map[string]any{
					"name": fld.Name(), "type": fty, "embedded": fld.Anonymous()})
			}
			out = append(out, map[string]any{
				"name": qname,
				"def":  map[string]any{"kind": "struct", "fields": fields},
			})
			e.namedStructTypes = append(e.namedStructTypes, named)
			continue
		}
		if iface, isInterface := named.Underlying().(*types.Interface); isInterface {
			// CONSTRAINT-ONLY interfaces (type-set terms — `~int | ~int8`,
			// `comparable` embeddings) are not value types: go/types
			// forbids using them outside a constraint, all their content
			// is static, and emitting them as ordinary interface TypeDefs
			// would declare an EMPTY requirement list that every dynamic
			// type vacuously satisfies (the audit-finding-0 hazard class).
			// Nothing of them reaches runtime; skip.
			if !iface.IsMethodSet() {
				continue
			}
			// Interface types get an `interface` TypeDef (the satisfaction
			// requirements, emitted for the whole seen set in emitProgram).
			// DISPATCH is separate: per-method table entries with the same
			// wire shape as a concrete method (recv + params + results),
			// marked "interface": true, with NO body.
			e.noteInterface(qname, iface)
			recvTy := map[string]any{"kind": "interface", "name": qname}
			for i := 0; i < iface.NumMethods(); i++ {
				m := iface.Method(i)
				sig := m.Type().(*types.Signature)
				params, err := e.emitParams(sig.Params())
				if err != nil {
					return nil, nil, err
				}
				results, err := e.emitResults(sig.Results())
				if err != nil {
					return nil, nil, err
				}
				ifaceMethods = append(ifaceMethods, map[string]any{
					"name":      m.Name(),
					"recvType":  qname,
					"recv":      map[string]any{"id": "$recv", "type": recvTy},
					"params":    params,
					"results":   results,
					"variadic":  sig.Variadic(),
					"interface": true,
				})
			}
			continue
		}
		// Other defined types (over primitives, maps, arrays, slices) are
		// IDENTITY-BEARING (interfaces campaign S2, BUG-004 item 2): they
		// emit kind "defined" with their underlying, so GoCore keeps the
		// identity for boxing/asserts/method sets while resolving defaults,
		// conversions, and equality through the underlying. True Go aliases
		// (`type T = U`) never reach this loop: go/types materializes them
		// as *types.Alias, so the *types.Named cast above filters them and
		// their use sites emit U directly.
		underlying, err := e.emitType(named.Underlying())
		if err != nil {
			return nil, nil, err
		}
		out = append(out, map[string]any{
			"name": qname,
			"def":  map[string]any{"kind": "defined", "target": underlying},
		})
	}
	return out, ifaceMethods, nil
}

// ---- functions ----

func (e *emitter) emitFuncDecl(d *ast.FuncDecl) (map[string]any, error) {
	sig := e.info.Defs[d.Name].Type().(*types.Signature)
	e.curResults = sig.Results()
	// Function-scoped receive flag (BUG-023/BUG-026): drives the len/cap
	// hoist that keeps spec-ordered evaluations lexically ordered against
	// hoisted receives, in every emission path of this body.
	e.fnHasRecv = d.Body != nil && containsRecv(d.Body)

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
		// Go's variadic marker on the LAST parameter. Carried verbatim so
		// interface satisfaction can compare it: `M(xs ...int)` and
		// `M(xs []int)` have the same param TYPE (`[]int`) but are
		// different method signatures, so a type declaring one does not
		// implement an interface requiring the other (pre-merge audit
		// 2026-07-31, finding 0).
		"variadic": sig.Variadic(),
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
		name, ok := e.namedTypeName(defType)
		if !ok {
			return nil, unsup("method on anonymous type %s", defType)
		}
		fn["recv"] = map[string]any{"id": localName(recv), "type": rty}
		fn["recvType"] = name
	}

	if d.Body == nil {
		return nil, unsup("bodyless function %s", d.Name.Name)
	}
	savedBranch, savedGoto := e.branchLabels, e.gotoLabels
	savedSeg, savedPC, savedLoop := e.gotoSeg, e.gotoPC, e.gotoLoop
	e.branchLabels, e.gotoLabels = scanLabelUses(d.Body)
	e.gotoSeg, e.gotoPC, e.gotoLoop = nil, "", ""
	var body any
	var berr error
	if len(e.gotoLabels) > 0 {
		body, berr = e.emitGotoBody(d.Body)
	} else {
		body, berr = e.emitBlock(d.Body)
	}
	e.branchLabels, e.gotoLabels = savedBranch, savedGoto
	e.gotoSeg, e.gotoPC, e.gotoLoop = savedSeg, savedPC, savedLoop
	if berr != nil {
		return nil, berr
	}
	fn["body"] = body
	return fn, nil
}

// scanLabelUses collects the labels a function body references by labeled
// break/continue and by goto, WITHOUT descending into nested func literals
// (a label's scope never crosses a function boundary — go/types enforces
// it; each literal body gets its own scan).
func scanLabelUses(body *ast.BlockStmt) (branch, gotos map[string]bool) {
	branch = map[string]bool{}
	gotos = map[string]bool{}
	ast.Inspect(body, func(n ast.Node) bool {
		if _, isLit := n.(*ast.FuncLit); isLit {
			return false
		}
		if br, ok := n.(*ast.BranchStmt); ok && br.Label != nil {
			switch br.Tok {
			case token.BREAK, token.CONTINUE:
				branch[br.Label.Name] = true
			case token.GOTO:
				gotos[br.Label.Name] = true
			}
		}
		return true
	})
	return branch, gotos
}

// emitLabeled lowers a labeled statement by how its label is USED:
// goto targets go through the dispatch-loop restructuring (stage 3);
// labeled-break/continue targets wrap the loop-forming statement in a
// wire "labeled" node (the decoder attaches the machine label DIRECTLY
// around the loop — the contHeadLabel placement invariant); an inert
// label (unreferenced) has no runtime meaning and drops.
func (e *emitter) emitLabeled(st *ast.LabeledStmt) (any, error) {
	name := st.Label.Name
	if e.gotoLabels[name] {
		// A goto-target label reaching emitStmt is either a registered
		// segment start whose statement ALSO carries break/continue uses
		// (emitGotoBody keeps the label on the statement for the branch
		// wrapper below), or a label NOT at the top level of the
		// restructured body — outside the envelope, fail closed.
		if _, consumed := e.gotoSeg[name]; !consumed {
			return nil, unsup("goto target label %s not at function body top level", name)
		}
	}
	if !e.branchLabels[name] {
		if _, isEmpty := st.Stmt.(*ast.EmptyStmt); isEmpty {
			return map[string]any{"stmt": "block", "body": []any{}}, nil
		}
		return e.emitStmt(st.Stmt)
	}
	switch st.Stmt.(type) {
	case *ast.ForStmt, *ast.RangeStmt, *ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.SelectStmt:
		w, err := e.emitStmt(st.Stmt)
		if err != nil {
			return nil, err
		}
		m, ok := w.(map[string]any)
		if !ok {
			return nil, unsup("labeled statement lowering shape")
		}
		switch m["stmt"] {
		case "for", "range", "breakable":
			return map[string]any{"stmt": "labeled", "label": name, "body": m}, nil
		case "block":
			// The per-iteration for desugar wraps its loop in a block of
			// seed statements; the label belongs on the inner loop node.
			if list, ok := m["body"].([]any); ok && len(list) > 0 {
				if inner, ok := list[len(list)-1].(map[string]any); ok && inner["stmt"] == "for" {
					list[len(list)-1] = map[string]any{
						"stmt": "labeled", "label": name, "body": inner}
					m["body"] = list
					return m, nil
				}
			}
			return nil, unsup("labeled statement lowering shape (block without trailing loop)")
		default:
			return nil, unsup("labeled statement lowering shape %v", m["stmt"])
		}
	default:
		// go/types only accepts break/continue labels on for/switch/select;
		// anything else is defensive.
		return nil, unsup("labeled break/continue target %T", st.Stmt)
	}
}

// degradeGotoTarget rewrites a "declare" wire target of a SOURCE-level
// name to a plain "var" target: under the goto restructuring the cell is
// pre-declared by the hoist, and re-executing the statement (a backward
// jump) re-assigns it. Lowering temps ($-prefixed) keep their declares —
// they are declared and consumed within one statement's lowering, inside
// one sweep.
func degradeGotoTarget(t any) any {
	m, ok := t.(map[string]any)
	if !ok {
		return t
	}
	if m["target"] == "declare" {
		if id, ok := m["id"].(string); ok && !strings.HasPrefix(id, "$") {
			return map[string]any{"target": "var", "id": id}
		}
	}
	return t
}

// degradeGotoDeclares post-processes a segment's top-level wire nodes:
// source declarations become assignments to the hoisted cells ("var"
// nodes turn into default/init assignments; declare targets in
// assign/type-assert/make/append/... nodes become var targets). Only the
// TOP level is touched — deeper blocks re-execute wholesale with their
// own scopes, which is Go's re-declaration semantics.
func degradeGotoDeclares(stmts []any) []any {
	out := make([]any, 0, len(stmts))
	for _, s := range stmts {
		m, ok := s.(map[string]any)
		if !ok {
			out = append(out, s)
			continue
		}
		if m["stmt"] == "var" {
			decls, _ := m["decls"].([]any)
			conv := []any{}
			for _, d := range decls {
				dm, ok := d.(map[string]any)
				if !ok {
					continue
				}
				id, _ := dm["id"].(string)
				if id == "_" {
					// Blank decl: no cell exists (the hoist collector
					// skips blanks — there is no variable), but the
					// initializer must still run each sweep. Keep the
					// DECLARATION, scoped to this conversion block,
					// which re-executes wholesale per sweep — the
					// non-goto blank path's observable semantics.
					// (Audit-response 2026-08-04, F4: degrading to an
					// assignment produced an UNBOUND `_` — machine
					// stuck instead of a boundary refusal.)
					conv = append(conv, map[string]any{"stmt": "var",
						"decls": []any{d}})
					continue
				}
				rhs := dm["init"]
				if rhs == nil {
					// `var x T` re-executed resets to the zero value (Go:
					// a fresh variable).
					rhs = map[string]any{"expr": "default", "type": dm["type"]}
				}
				conv = append(conv, map[string]any{"stmt": "assign",
					"lhs": []any{map[string]any{"target": "var", "id": id}},
					"rhs": []any{rhs}})
			}
			out = append(out, map[string]any{"stmt": "block", "body": conv})
			continue
		}
		for _, key := range []string{"target", "okTarget"} {
			if t, has := m[key]; has {
				m[key] = degradeGotoTarget(t)
			}
		}
		if lhs, ok := m["lhs"].([]any); ok {
			for i := range lhs {
				lhs[i] = degradeGotoTarget(lhs[i])
			}
		}
		out = append(out, m)
	}
	return out
}

// addrEscapeRoot unwraps an expression whose ADDRESS is being taken
// (explicitly by `&`, or implicitly by slicing an array or by a
// pointer-receiver method's receiver) to the storage root: parens,
// field selections on non-pointer bases, and index expressions on
// arrays denote SUB-OBJECTS of their operand's storage, so the walk
// continues; a pointer indirection (explicit `*p`, a selector through a
// pointer, or slice/map indexing) reaches heap storage — no local
// cell's address is observed — so the walk stops (nil). Returns the
// root identifier when the addressed storage is (part of) that
// identifier's own cell. Missing type info walks CONSERVATIVELY toward
// the root (over-refusing is a narrowed envelope; under-refusing is
// unsound). Audit-response 2026-08-04: the previous check matched only
// `&x` / `x.M()` on a BARE identifier, so `&(x)`, `&s.f`, `&a[0]`,
// `a[:]`, and `s.f.M()` all escaped a hoisted cell silently.
func (e *emitter) addrEscapeRoot(x ast.Expr) *ast.Ident {
	for {
		switch v := x.(type) {
		case *ast.Ident:
			return v
		case *ast.ParenExpr:
			x = v.X
		case *ast.SelectorExpr:
			// Field selection on a value: sub-object of the base's
			// storage. Through a pointer: heap. (Method selections are
			// handled at their own inspect site, not here.)
			if bt := e.goTypeOf(v.X); bt != nil {
				if _, isPtr := bt.Underlying().(*types.Pointer); isPtr {
					return nil
				}
			}
			x = v.X
		case *ast.IndexExpr:
			// Indexing an ARRAY value: sub-object storage. Slice, map,
			// and pointer-to-array indexing indirect to heap cells.
			if bt := e.goTypeOf(v.X); bt != nil {
				if _, isArr := bt.Underlying().(*types.Array); !isArr {
					return nil
				}
			}
			x = v.X
		case *ast.StarExpr:
			// Explicit deref: the addressed storage is behind a pointer.
			return nil
		default:
			// Go's addressability rules limit `&` operands to the shapes
			// above plus composite literals / rvalue chains, which denote
			// FRESH storage per evaluation in both Go and the lowering.
			return nil
		}
	}
}

// hoistedAddrEscape reports the hoisted variable whose cell (or
// sub-object of it) would have its address observed by taking the
// address of x, or nil.
func (e *emitter) hoistedAddrEscape(x ast.Expr, hoisted map[types.Object]bool) *ast.Ident {
	id := e.addrEscapeRoot(x)
	if id == nil {
		return nil
	}
	if obj := e.info.Uses[id]; obj != nil && hoisted[obj] {
		return id
	}
	return nil
}

// Kinds of address escape found by findAddrEscape.
const (
	escapeAddr  = "address-taken"
	escapeSlice = "array-sliced"
	escapeRecv  = "pointer-method-receiver"
)

type addrEscape struct {
	id   *ast.Ident
	kind string
}

// findAddrEscape scans root for the first position that observes the
// address of storage rooted (via addrEscapeRoot) in one of vars:
// explicit `&expr`; slice expressions on array operands (`a[:]` is
// `(&a)[:]`; slicing a slice/string/*array reads a header or derefs);
// pointer-receiver METHOD calls and method values, whose receiver chain
// is addressed implicitly — including nested field paths (`s.f.M()`)
// and parens, skipped when the operand is itself pointer-typed (the
// pointer value IS the receiver — no implicit address of its cell).
// Conservative corner (recorded in the design note): a pointer-receiver
// method promoted through an embedded POINTER field of a non-pointer
// root is reported although the address taken is behind that pointer.
// Shared by the goto restructuring's fidelity envelope and the
// Go >= 1.22 per-iteration loop-variable trigger (delta-review round 2,
// 2026-08-04: the trigger detected only func-literal captures, so an
// address escape of a for-clause variable took the shared-cell lowering
// silently).
func (e *emitter) findAddrEscape(root ast.Node, vars map[types.Object]bool) *addrEscape {
	var found *addrEscape
	ast.Inspect(root, func(n ast.Node) bool {
		if found != nil {
			return false
		}
		switch nn := n.(type) {
		case *ast.UnaryExpr:
			if nn.Op == token.AND {
				if id := e.hoistedAddrEscape(nn.X, vars); id != nil {
					found = &addrEscape{id: id, kind: escapeAddr}
				}
			}
		case *ast.SliceExpr:
			isArr := true // missing type info: conservative
			if t := e.goTypeOf(nn.X); t != nil {
				_, isArr = t.Underlying().(*types.Array)
			}
			if isArr {
				if id := e.hoistedAddrEscape(nn.X, vars); id != nil {
					found = &addrEscape{id: id, kind: escapeSlice}
				}
			}
		case *ast.SelectorExpr:
			selInfo, ok := e.info.Selections[nn]
			if !ok || selInfo.Kind() != types.MethodVal {
				break
			}
			fn, isFn := selInfo.Obj().(*types.Func)
			if !isFn {
				break
			}
			sig, isSig := fn.Type().(*types.Signature)
			if !isSig || sig.Recv() == nil {
				break
			}
			if _, isPtr := sig.Recv().Type().Underlying().(*types.Pointer); !isPtr {
				break
			}
			if ot := e.goTypeOf(nn.X); ot != nil {
				if _, opIsPtr := ot.Underlying().(*types.Pointer); opIsPtr {
					break
				}
			}
			if id := e.hoistedAddrEscape(nn.X, vars); id != nil {
				found = &addrEscape{id: id, kind: escapeRecv}
			}
		}
		return found == nil
	})
	return found
}

// emitGotoBody lowers a function body containing `goto` into a
// program-counter dispatch loop over the body's top-level segments,
// riding on the stage-2 machine labels
// (docs/2026-08-04_control-flow-design.md, stage 3):
//
//	{ var <hoisted top-level decls>; $pc := 0
//	  $gotoN: for { if $pc <= 0 { seg0 }; if $pc <= 1 { seg1 }; ...; break } }
//
// `goto L` (any depth, same function) becomes
// `$pc = seg(L); continue-to $gotoN`. Segments share the hoisted scope
// across sweeps; top-level declarations become assignments. The fidelity
// ENVELOPE is checked here and fails closed (the design note's three
// rejections): goto targets must be top-level labels; hoisted variables
// must not be captured, address-taken (incl. as pointer-method
// receivers), or shadow an outer name that the body also uses.
func (e *emitter) emitGotoBody(b *ast.BlockStmt) (map[string]any, error) {
	seq := e.tmpSeq
	e.tmpSeq++
	pcVar := "$pc" + itoa(seq)
	loopLabel := "$goto" + itoa(seq)

	// 1. Split into segments at top-level goto-target labels.
	type segment struct{ stmts []ast.Stmt }
	segs := []segment{{}}
	segIdx := map[string]int{}
	for _, s := range b.List {
		inner := s
		segLabels := []string{}
		for {
			ls, ok := inner.(*ast.LabeledStmt)
			if !ok || !e.gotoLabels[ls.Label.Name] {
				break
			}
			segLabels = append(segLabels, ls.Label.Name)
			if e.branchLabels[ls.Label.Name] {
				// keep the label on the statement: emitLabeled wraps it
				// for break/continue (it sees the label as consumed).
				break
			}
			inner = ls.Stmt
		}
		if len(segLabels) > 0 {
			segs = append(segs, segment{})
			for _, l := range segLabels {
				segIdx[l] = len(segs) - 1
			}
		}
		segs[len(segs)-1].stmts = append(segs[len(segs)-1].stmts, inner)
	}
	for name := range e.gotoLabels {
		if _, ok := segIdx[name]; !ok {
			return nil, unsup("goto target label %s not at function body top level", name)
		}
	}

	// 2. Collect the top-level declared variables (the hoist set).
	type hoistVar struct {
		obj  types.Object
		name string
	}
	hoisted := []hoistVar{}
	seenObj := map[types.Object]bool{}
	collect := func(id *ast.Ident) {
		if id.Name == "_" {
			return
		}
		if obj := e.info.Defs[id]; obj != nil && !seenObj[obj] {
			seenObj[obj] = true
			hoisted = append(hoisted, hoistVar{obj: obj, name: id.Name})
		}
	}
	for _, seg := range segs {
		for _, s := range seg.stmts {
			stmt := s
			for {
				ls, ok := stmt.(*ast.LabeledStmt)
				if !ok {
					break
				}
				stmt = ls.Stmt
			}
			switch d := stmt.(type) {
			case *ast.AssignStmt:
				if d.Tok == token.DEFINE {
					for _, l := range d.Lhs {
						if id, ok := l.(*ast.Ident); ok {
							collect(id)
						}
					}
				}
			case *ast.DeclStmt:
				if gd, ok := d.Decl.(*ast.GenDecl); ok && gd.Tok == token.VAR {
					for _, spec := range gd.Specs {
						if vs, ok := spec.(*ast.ValueSpec); ok {
							for _, n := range vs.Names {
								collect(n)
							}
						}
					}
				}
			}
		}
	}

	// 3. The fidelity envelope, fail-closed.
	hoistedObjs := map[types.Object]bool{}
	for _, hv := range hoisted {
		hoistedObjs[hv.obj] = true
	}
	var envErr error
	ast.Inspect(b, func(n ast.Node) bool {
		if envErr != nil {
			return false
		}
		if nn, ok := n.(*ast.FuncLit); ok {
			// A capture makes per-execution cell identity observable: a
			// backward jump re-executing the declaration gives Go a FRESH
			// cell but the hoisted lowering one shared cell. ANY use
			// inside a literal is a capture, so address escapes inside
			// literals are subsumed here.
			ast.Inspect(nn, func(m ast.Node) bool {
				if id, ok := m.(*ast.Ident); ok {
					if obj := e.info.Uses[id]; obj != nil && hoistedObjs[obj] {
						envErr = unsup("goto function hoists a captured variable %s", id.Name)
					}
				}
				return envErr == nil
			})
			return false
		}
		return envErr == nil
	})
	if envErr == nil {
		// Address escapes (explicit &, array slicing, pointer-receiver
		// methods) — the shared tracer, findAddrEscape.
		if esc := e.findAddrEscape(b, hoistedObjs); esc != nil {
			switch esc.kind {
			case escapeSlice:
				envErr = unsup("goto function hoists variable %s whose array storage is sliced", esc.id.Name)
			case escapeRecv:
				envErr = unsup("goto function hoists variable %s used as a pointer-method receiver", esc.id.Name)
			default:
				envErr = unsup("goto function hoists an address-taken variable %s", esc.id.Name)
			}
		}
	}
	if envErr != nil {
		return nil, envErr
	}
	// Shadow check: hoisting a name to the body's head would capture uses
	// that Go statically resolves to an OUTER object of the same name
	// (params/results/package scope) — including a define's own RHS.
	names := map[string]types.Object{}
	for _, hv := range hoisted {
		names[hv.name] = hv.obj
	}
	ancestors := map[*types.Scope]bool{}
	if len(hoisted) > 0 {
		for sc := hoisted[0].obj.Parent(); sc != nil; sc = sc.Parent() {
			ancestors[sc] = true
		}
	}
	ast.Inspect(b, func(n ast.Node) bool {
		if envErr != nil {
			return false
		}
		if id, ok := n.(*ast.Ident); ok {
			if v, isHoistedName := names[id.Name]; isHoistedName {
				if obj := e.info.Uses[id]; obj != nil && obj != v && obj.Parent() != nil && ancestors[obj.Parent()] {
					envErr = unsup("goto function hoists variable %s shadowing an outer name in use", id.Name)
				}
			}
		}
		return envErr == nil
	})
	if envErr != nil {
		return nil, envErr
	}

	// 4. Hoisted declarations (default values) + program counter.
	outer := []any{}
	for _, hv := range hoisted {
		ty, err := e.emitType(hv.obj.Type())
		if err != nil {
			return nil, err
		}
		outer = append(outer, map[string]any{"stmt": "var",
			"decls": []any{map[string]any{"id": hv.name, "type": ty}}})
	}
	intTy := map[string]any{"kind": "int", "int": "int"}
	outer = append(outer, map[string]any{"stmt": "assign", "define": true,
		"lhs": []any{map[string]any{"target": "declare", "id": pcVar, "type": intTy}},
		"rhs": []any{map[string]any{"expr": "int", "value": "0", "type": intTy}}})

	// 5. Segments under the goto context; `$pc <= i` guards give normal
	// sequential fall-through within a sweep (pc changes only via goto,
	// which immediately re-enters the loop).
	savedSeg, savedPC, savedLoop := e.gotoSeg, e.gotoPC, e.gotoLoop
	e.gotoSeg, e.gotoPC, e.gotoLoop = segIdx, pcVar, loopLabel
	dispatch := []any{}
	var segErr error
	for i, seg := range segs {
		stmts, err := e.emitStmtList(seg.stmts)
		if err != nil {
			segErr = err
			break
		}
		stmts = degradeGotoDeclares(stmts)
		guard := map[string]any{"expr": "binary", "op": "<=",
			"x": map[string]any{"expr": "ident", "name": pcVar, "type": intTy},
			"y": map[string]any{"expr": "int", "value": itoa(i), "type": intTy}}
		dispatch = append(dispatch, map[string]any{"stmt": "if", "cond": guard,
			"then": map[string]any{"stmt": "block", "body": stmts}})
	}
	e.gotoSeg, e.gotoPC, e.gotoLoop = savedSeg, savedPC, savedLoop
	if segErr != nil {
		return nil, segErr
	}
	dispatch = append(dispatch, map[string]any{"stmt": "break"})
	loop := map[string]any{"stmt": "labeled", "label": loopLabel,
		"body": map[string]any{"stmt": "for",
			"body": map[string]any{"stmt": "block", "body": dispatch}}}
	outer = append(outer, loop)
	return map[string]any{"stmt": "block", "body": outer}, nil
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
	tup, ok := e.goTypeOf(c).(*types.Tuple)
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
		// A bare receive statement `<-ch` / `(<-ch)` (spec §Expression
		// statements: "receive operations can appear in statement
		// context") is receive-and-discard: the ZERO-target chan-recv
		// statement (BUG-024, audit S3+S8 — the expression-position hoist
		// left a residual ident the decoder rejected, taking the whole
		// package down).
		if ux, ok := ast.Unparen(st.X).(*ast.UnaryExpr); ok && ux.Op == token.ARROW {
			elemGo, err := e.chanElem(ux.X)
			if err != nil {
				return nil, err
			}
			elemTy, err := e.emitType(elemGo)
			if err != nil {
				return nil, err
			}
			chW, err := e.emitExpr(ux.X)
			if err != nil {
				return nil, err
			}
			return map[string]any{"stmt": "chan-recv", "targets": []any{}, "ch": chW, "elem": elemTy}, nil
		}
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
					case "close":
						return e.emitCloseStmt(call)
					default:
						// Any other builtin in STATEMENT position (a bare
						// `recover()`, `print`, ...) has no statement
						// lowering: refuse HERE so the decl quarantines
						// per-function. The old fall-through emitted the
						// builtin's EXPRESSION node inside an expr
						// statement, which the decoder rejects as a
						// whole-package error (found by
						// goroutines/spawn-edge/child-recovers, whose bare
						// deferred recover() took its package siblings
						// down — a fail-open, not a semantics gap).
						return nil, unsup("builtin %s in statement position", id.Name)
					}
				}
			}
			// slices.Sort at an integer element kind: the quorum-pilot
			// extern (docs/2026-07-30_quorum-extern-policy.md). Any other
			// slices.*/sort.* member falls through to the normal call
			// path and fails closed there (unresolvable package func).
			if sel, ok := call.Fun.(*ast.SelectorExpr); ok {
				if pkgIdent, ok := sel.X.(*ast.Ident); ok {
					if pkgName, ok := e.info.Uses[pkgIdent].(*types.PkgName); ok &&
						pkgName.Imported().Path() == "slices" {
						if sel.Sel.Name != "Sort" {
							return nil, unsup("slices.%s (only slices.Sort at integer elements is modeled)", sel.Sel.Name)
						}
						return e.emitSortStmt(call)
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
	case *ast.TypeSwitchStmt:
		return e.emitTypeSwitch(st)
	case *ast.SendStmt:
		// `ch <- v` (channels arc slice 1): channel then value, evaluated
		// in that order (spec §Send statements; pinned by
		// channels/make-edge/ordinary-send-eval-order — effectful operands
		// ride the A-normal-form hoists, which preserve source order).
		ch, ok := e.applySubst(e.goTypeOf(st.Chan)).Underlying().(*types.Chan)
		if !ok {
			return nil, unsup("send on non-channel %s", e.goTypeOf(st.Chan))
		}
		chW, err := e.emitExpr(st.Chan)
		if err != nil {
			return nil, err
		}
		valW, err := e.emitExpr(st.Value)
		if err != nil {
			return nil, err
		}
		valW, err = e.wrapInterfaceConversion(ch.Elem(), e.goTypeOf(st.Value), valW)
		if err != nil {
			return nil, err
		}
		elemTy, err := e.emitType(ch.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "chan-send", "ch": chW, "value": valW, "elem": elemTy}, nil
	case *ast.SelectStmt:
		return e.emitSelect(st)
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
				// `defer close(ch)` (audit S6 — the canonical channel
				// defer idiom): defer a synthetic one-parameter closer,
				// which gives Go's semantics exactly through the existing
				// defer machinery — the channel operand evaluates NOW, the
				// close (and any close-of-closed/nil panic) fires at frame
				// exit as the deferred invocation's panic.
				if id.Name == "close" && len(st.Call.Args) == 1 {
					return e.emitDeferClose(st.Call)
				}
				return nil, unsup("defer of builtin %s", id.Name)
			}
		}
		callee, err := e.emitExpr(st.Call.Fun)
		if err != nil {
			return nil, err
		}
		var dsig *types.Signature
		if tv, ok := e.typesEntry(st.Call.Fun); ok {
			dsig, _ = tv.Type.Underlying().(*types.Signature)
		}
		args, err := e.emitCallArgs(dsig, st.Call)
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "defer", "callee": callee, "args": args}, nil
	case *ast.GoStmt:
		// `go f(args)` (channels arc slice 2): the function value and
		// parameters evaluate NOW, in the spawning goroutine (spec §Go
		// statements) — the defer wire shape with a "go" head; the
		// machine's pool performs the spawn. Builtin callees are
		// restricted as for expression statements and none is modeled in
		// spawn position — fail closed.
		if id, ok := st.Call.Fun.(*ast.Ident); ok {
			if _, isBuiltin := e.info.Uses[id].(*types.Builtin); isBuiltin {
				return nil, unsup("go of builtin %s", id.Name)
			}
		}
		callee, err := e.emitExpr(st.Call.Fun)
		if err != nil {
			return nil, err
		}
		var gsig *types.Signature
		if tv, ok := e.typesEntry(st.Call.Fun); ok {
			gsig, _ = tv.Type.Underlying().(*types.Signature)
		}
		args, err := e.emitCallArgs(gsig, st.Call)
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "go", "callee": callee, "args": args}, nil
	case *ast.LabeledStmt:
		return e.emitLabeled(st)
	case *ast.BranchStmt:
		switch st.Tok {
		case token.BREAK:
			if st.Label != nil {
				return map[string]any{"stmt": "break-to", "label": st.Label.Name}, nil
			}
			return map[string]any{"stmt": "break"}, nil
		case token.CONTINUE:
			if st.Label != nil {
				return map[string]any{"stmt": "continue-to", "label": st.Label.Name}, nil
			}
			return map[string]any{"stmt": "continue"}, nil
		case token.GOTO:
			// `goto L` under the dispatch-loop restructuring
			// (emitGotoBody): set the program counter to L's segment and
			// re-enter the dispatch loop via the stage-2 machine signal —
			// which unwinds out of any enclosing blocks/loops/switches,
			// exactly Go's out-of-block jump. No context (or a label that
			// is not a registered top-level segment) fails closed.
			if st.Label == nil {
				return nil, unsup("goto without label")
			}
			idx, ok := e.gotoSeg[st.Label.Name]
			if !ok {
				return nil, unsup("goto target label %s not at function body top level", st.Label.Name)
			}
			intTy := map[string]any{"kind": "int", "int": "int"}
			return map[string]any{"stmt": "block", "body": []any{
				map[string]any{"stmt": "assign",
					"lhs": []any{map[string]any{"target": "var", "id": e.gotoPC}},
					"rhs": []any{map[string]any{"expr": "int", "value": itoa(idx), "type": intTy}}},
				map[string]any{"stmt": "continue-to", "label": e.gotoLoop},
			}}, nil
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
	// Interface-typed results: box the returned value when its static type is
	// non-interface (wrapInterfaceConversion; replaces the fail-closed guard).
	wrapResult := func(i int, rt types.Type, w any) (any, error) {
		if e.curResults == nil || i >= e.curResults.Len() {
			return w, nil
		}
		return e.wrapInterfaceConversion(e.curResults.At(i).Type(), rt, w)
	}
	// `return f()` forwarding a multi-value call: splat into temps and
	// return the temps (the hoisted call statement is spliced before the
	// return by the A-normal-form machinery). Interface-typed result slots
	// wrap the individual temps.
	if len(st.Results) == 1 {
		if call, ok := st.Results[0].(*ast.CallExpr); ok {
			if tup, isTup := e.goTypeOf(call).(*types.Tuple); isTup {
				idents, err := e.splatMultiCall(call)
				if err != nil {
					return nil, err
				}
				for i := 0; i < len(idents) && i < tup.Len(); i++ {
					w, err := wrapResult(i, tup.At(i).Type(), idents[i])
					if err != nil {
						return nil, err
					}
					idents[i] = w
				}
				return map[string]any{"stmt": "return", "results": idents}, nil
			}
		}
	}
	results := []any{}
	for i, r := range st.Results {
		w, err := e.emitExpr(r)
		if err != nil {
			return nil, err
		}
		w, err = wrapResult(i, e.goTypeOf(r), w)
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

// wrapInterfaceConversion boxes an emitted expression when a value of
// non-interface static type flows into an interface-typed slot (the
// interfaces campaign's real conversion; replaces the fail-closed guard,
// BUG-006). Untyped nil stays bare (a nil interface IS nil); an
// interface-typed source needs no wrap (Go never double-boxes).
func (e *emitter) wrapInterfaceConversion(target types.Type, rhs types.Type, operand any) (any, error) {
	// Substitute the active instantiation FIRST (mono.go): whether a slot
	// is interface-typed is a property of the INSTANTIATED types (a `T`
	// slot at `T = any` boxes; at `T = int` it does not).
	target = e.applySubst(target)
	rhs = e.applySubst(rhs)
	// Untyped nil into a NILABLE NON-INTERFACE slot takes the slot's
	// type (spec §Assignability: nil is assignable to pointer, function,
	// slice, map, channel, and interface types) — ONE mechanism for
	// every assignable context that flows through this wrap (BUG-016,
	// arc-final audit F6, 2026-08-06; generalizes the audit-response M1
	// map-literal fix). Same kind restriction as M1: DIRECT
	// slice/map/pointer only — func-typed and defined-typed slots keep
	// the bare-nil base emission (the machine's nil-literal arm rejects
	// their typed nil, BUG-014's boundary); interface slots keep the
	// bare nil below (a nil interface IS nil).
	if b, ok := rhs.(*types.Basic); ok && b.Kind() == types.UntypedNil && target != nil && !types.IsInterface(target) {
		switch types.Unalias(target).(type) {
		case *types.Slice, *types.Map, *types.Pointer:
			tw, err := e.emitType(target)
			if err != nil {
				return nil, err
			}
			return map[string]any{"expr": "nil", "type": tw}, nil
		}
		return operand, nil
	}
	if target == nil || !types.IsInterface(target) {
		return operand, nil
	}
	if rhs == nil {
		return operand, nil
	}
	if b, ok := rhs.(*types.Basic); ok && b.Kind() == types.UntypedNil {
		return operand, nil
	}
	if types.IsInterface(rhs) {
		return operand, nil
	}
	targetWire, err := e.emitType(target)
	if err != nil {
		return nil, err
	}
	dynWire, err := e.emitType(rhs)
	if err != nil {
		return nil, err
	}
	return map[string]any{"expr": "to-interface", "target": targetWire, "dynamic": dynWire, "operand": operand}, nil
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
	return e.goTypeOf(l)
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
			if mt, ok := e.goTypeOf(ix.X).Underlying().(*types.Map); ok {
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

	// Comma-ok type assertion `v, ok := x.(T)` / `v, ok = x.(T)`: a dedicated
	// statement (the map comma-ok pattern), targets in the ordinary assign
	// target encoding — on `:=`, v declares as T and ok as bool via Defs.
	if len(st.Lhs) == 2 && len(st.Rhs) == 1 {
		if ta, isTA := ast.Unparen(st.Rhs[0]).(*ast.TypeAssertExpr); isTA && ta.Type != nil {
			target, err := e.emitAssignTarget(st.Lhs[0], define)
			if err != nil {
				return nil, err
			}
			okTarget, err := e.emitAssignTarget(st.Lhs[1], define)
			if err != nil {
				return nil, err
			}
			operand, err := e.emitExpr(ta.X)
			if err != nil {
				return nil, err
			}
			targetTy, err := e.emitType(e.goTypeOf(ta.Type))
			if err != nil {
				return nil, err
			}
			return map[string]any{"stmt": "type-assert", "target": target,
				"okTarget": okTarget, "expr": operand, "targetType": targetTy}, nil
		}
	}

	// Channel receive statement forms `v = <-ch` / `v, ok := <-ch` / …
	// (channels arc slice 1): the dedicated chan-recv statement carries
	// Go's assignment operand order (target addresses first, then the
	// channel — pinned by ordinary-receive-eval-order).
	if len(st.Lhs) >= 1 && len(st.Lhs) <= 2 && len(st.Rhs) == 1 {
		if ux, isU := ast.Unparen(st.Rhs[0]).(*ast.UnaryExpr); isU && ux.Op == token.ARROW {
			return e.emitChanRecvAssign(st, ux, define)
		}
	}

	// Map element assignment `m[k] = v` is a map store, not an addressed
	// index (maps are not addressable).
	if !define && len(st.Lhs) == 1 && len(st.Rhs) == 1 {
		if ix, ok := st.Lhs[0].(*ast.IndexExpr); ok {
			if m, ok := e.goTypeOf(ix.X).Underlying().(*types.Map); ok {
				base, err := e.emitExpr(ix.X)
				if err != nil {
					return nil, err
				}
				index, err := e.emitExpr(ix.Index)
				if err != nil {
					return nil, err
				}
				index, err = e.wrapInterfaceConversion(m.Key(), e.goTypeOf(ix.Index), index)
				if err != nil {
					return nil, err
				}
				value, err := e.emitExpr(st.Rhs[0])
				if err != nil {
					return nil, err
				}
				value, err = e.wrapInterfaceConversion(m.Elem(), e.goTypeOf(st.Rhs[0]), value)
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
	// Interface-typed targets: per-pair RHSes wrap at emission (below); a
	// multi-value call's tuple components cannot be wrapped post-hoc (the
	// call node produces the whole tuple), so that shape stays a refusal.
	if len(st.Rhs) == 1 && len(st.Lhs) > 1 {
		if tup, ok := e.goTypeOf(st.Rhs[0]).(*types.Tuple); ok && tup.Len() == len(st.Lhs) {
			for i, l := range st.Lhs {
				target := e.applySubst(e.assignTargetType(l, define))
				comp := tup.At(i).Type()
				if target != nil && types.IsInterface(target) && !types.IsInterface(comp) {
					if b, isB := comp.(*types.Basic); !isB || b.Kind() != types.UntypedNil {
						return nil, unsup("implicit interface conversion in multi-value assignment (interfaces campaign, deferred)")
					}
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
			if tup, ok := e.goTypeOf(call).(*types.Tuple); ok && tup.Len() > 1 {
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
					// Single-value call into an interface-typed target: box
					// the call's result (multi-value stays refused above).
					if !isMultiValue && len(st.Lhs) == 1 {
						node, err = e.wrapInterfaceConversion(
							e.assignTargetType(st.Lhs[0], define), e.goTypeOf(call), node)
						if err != nil {
							return nil, err
						}
					}
					return map[string]any{"stmt": "assign", "define": define, "lhs": lhs, "rhs": []any{node}}, nil
				}
			}
		}
	}
	rhs := []any{}
	for i, r := range st.Rhs {
		w, err := e.emitExpr(r)
		if err != nil {
			return nil, err
		}
		// Capturing define: pre-bind EVERY RHS to a hoisted temp (uniformly,
		// preserving left-to-right evaluation), so the values are read in
		// the outer scope before the declarations take effect.
		if captures {
			w, err = e.hoist(w, e.goTypeOf(r))
			if err != nil {
				return nil, err
			}
		}
		// Per-pair interface-typed target: box the (possibly temp-bound)
		// value. Wrapping AFTER the hoist keeps the temp at the value's
		// static type; the boxed view is built where it is consumed.
		if len(st.Rhs) == len(st.Lhs) {
			w, err = e.wrapInterfaceConversion(
				e.assignTargetType(st.Lhs[i], define), e.goTypeOf(r), w)
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
		// A package-level variable writes through its statically resolved
		// cell address (init slice). Uses covers ordinary writes; Defs
		// covers the synthesized $pkginit assignments, whose Lhs are the
		// ORIGINAL declaring idents.
		obj := e.info.Uses[id]
		if obj == nil {
			obj = e.info.Defs[id]
		}
		if v, ok := e.isPackageVar(obj); ok {
			ga, ok := e.globalAddr(v)
			if !ok {
				return nil, unsup("package-level variable %s has no seeded cell", id.Name)
			}
			return map[string]any{"target": "addr", "expr": ga}, nil
		}
		return map[string]any{"target": "var", "id": id.Name}, nil
	}
	// Non-ident lvalue (field, index, deref): emit as an addressed location.
	return e.emitLValue(l)
}

func (e *emitter) emitDeclStmt(st *ast.DeclStmt) (any, error) {
	gd, ok := st.Decl.(*ast.GenDecl)
	// A const declaration is a no-op statement: go/types folds every USE
	// of the constant to its value (emitIdent), so nothing lowers here.
	if ok && gd.Tok == token.CONST {
		return map[string]any{"stmt": "block", "body": []any{}}, nil
	}
	// A function-LOCAL type declaration registers in the global type
	// table (a Go type declaration has no runtime effect — jumping over
	// one with goto is legal) and lowers to a no-op statement.
	// emitProgram refuses duplicate TypeIds, so a local type colliding
	// with another declaration fails closed rather than aliasing.
	if ok && gd.Tok == token.TYPE {
		tds, ims, err := e.emitGenDeclTypes(gd)
		if err != nil {
			return nil, err
		}
		e.localTypeDefs = append(e.localTypeDefs, tds...)
		e.localIfaceMethods = append(e.localIfaceMethods, ims...)
		return map[string]any{"stmt": "block", "body": []any{}}, nil
	}
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
				init, err := e.emitExpr(vs.Values[i])
				if err != nil {
					return nil, err
				}
				if e.containsVarUse(vs.Values[i], declNames) {
					init, err = e.hoist(init, e.goTypeOf(vs.Values[i]))
					if err != nil {
						return nil, err
					}
				}
				// Interface-typed declaration with a non-interface
				// initializer: box (after any hoist, so the temp keeps the
				// value's static type). A multi-value initializer's tuple
				// components cannot be wrapped post-hoc — deferred.
				if _, isTup := e.goTypeOf(vs.Values[i]).(*types.Tuple); isTup {
					if types.IsInterface(e.applySubst(obj.Type())) {
						return nil, unsup("implicit interface conversion in multi-value assignment (interfaces campaign, deferred)")
					}
				} else {
					init, err = e.wrapInterfaceConversion(
						obj.Type(), e.goTypeOf(vs.Values[i]), init)
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
	// The plain lowering declares the variable once outside the loop (one
	// shared cell) — a silent wrong answer for escaping captures
	// (pre-merge audit 2026-07-25; range loops are per-iteration already
	// and are fine). Loops whose for-clause variables are captured by a
	// literal BODY take the per-iteration desugar (`emitForPerIteration`);
	// `defer f(i)` is fine on the plain path — args evaluate at defer time.
	if st.Init != nil {
		loopVars := map[types.Object]bool{}
		loopVarIdents := []*ast.Ident{}
		if as, ok := st.Init.(*ast.AssignStmt); ok && as.Tok == token.DEFINE {
			for _, l := range as.Lhs {
				if id, ok := l.(*ast.Ident); ok && id.Name != "_" {
					if obj := e.info.Defs[id]; obj != nil {
						loopVars[obj] = true
						loopVarIdents = append(loopVarIdents, id)
					}
				}
			}
		}
		if len(loopVars) > 0 {
			// The scan covers the body AND the condition and post
			// statement (audit-response 2026-08-04, F2: it scanned only
			// the body, so a capturing literal in the condition — newly
			// accepted since condPre — or in the post, a hole predating
			// this slice, took the shared-cell lowering silently). Per
			// Go >= 1.22, iteration k's post runs on iteration k+1's
			// freshly declared variable, and the condition and body of
			// iteration k+1 use that same cell — exactly the desugar's
			// top-of-iteration fresh cell, so cond/post captures ride
			// the same per-iteration path (differentially pinned by
			// for-loopvar-cond-capture / for-loopvar-post-capture).
			captured := false
			scanForCapture := func(root ast.Node) {
				ast.Inspect(root, func(n ast.Node) bool {
					lit, ok := n.(*ast.FuncLit)
					if !ok {
						return !captured
					}
					ast.Inspect(lit, func(m ast.Node) bool {
						if id, ok := m.(*ast.Ident); ok {
							if obj := e.info.Uses[id]; obj != nil && loopVars[obj] {
								captured = true
							}
						}
						return !captured
					})
					return false
				})
			}
			scanForCapture(st.Body)
			if st.Cond != nil {
				scanForCapture(st.Cond)
			}
			if st.Post != nil {
				scanForCapture(st.Post)
			}
			// Cell identity also escapes WITHOUT a func literal:
			// explicit &i, slicing an array loop variable, or a
			// pointer-receiver method on (a chain rooting at) the loop
			// variable — the same escape shapes as the goto envelope,
			// traced by the shared findAddrEscape. The func-literal-only
			// predicate PRE-DATES this slice; delta-review round 2
			// (2026-08-04) exhibited silent wrong answers (333 vs Go's
			// 12) for all three shapes. The carrier-pointer desugar is
			// correct for them: each iteration's escape observes that
			// iteration's own fresh cell (differentially pinned by
			// for-loopvar-addr-escape / -ptr-recv / -array-slice).
			escaped := captured ||
				e.findAddrEscape(st.Body, loopVars) != nil ||
				(st.Cond != nil && e.findAddrEscape(st.Cond, loopVars) != nil) ||
				(st.Post != nil && e.findAddrEscape(st.Post, loopVars) != nil)
			if escaped {
				return e.emitForPerIteration(st, loopVarIdents)
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
		// The loop condition is re-evaluated each iteration. Its hoists
		// (calls/allocations) are legal because the decoder re-tests the
		// condition INSIDE the loop body: they travel as `condPre`,
		// spliced immediately before each test.
		saved := e.hoisted
		e.hoisted = nil
		cond, err := e.emitExpr(st.Cond)
		condHoists := e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, err
		}
		node["cond"] = cond
		if len(condHoists) > 0 {
			node["condPre"] = condHoists
		}
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

// emitForPerIteration lowers a ForClause loop whose loop variables are
// captured by a func literal in the body. Go >= 1.22: each iteration has
// its OWN copy of the variables, "declared before executing the post
// statement and initialized to the value of the previous iteration's
// variable at that moment". Desugar with a carrier POINTER so `continue`
// needs no copy-back path (docs/2026-08-04_control-flow-design.md):
//
//	{ i := <init>; $lvp := &i; $lvf := true
//	  for { block {
//	    i := *$lvp; $lvp = &i            // fresh cell per iteration
//	    if $lvf { $lvf = false } else { post }   // post on the fresh i
//	    condPre...; if cond {} else { break }
//	    body } } }
//
// Everything per-iteration happens at the TOP of the iteration, so a
// `continue` (which re-enters the loop) carries the current cell's final
// value into the next iteration through the pointer. Captures see one
// distinct cell per iteration.
func (e *emitter) emitForPerIteration(st *ast.ForStmt, vars []*ast.Ident) (any, error) {
	seq := e.tmpSeq
	e.tmpSeq++
	boolTy := map[string]any{"kind": "bool"}
	outer := []any{}
	// Seed cells: the init statement runs once, declaring the variables
	// under their own names in the outer scope (iteration 0's source).
	{
		saved := e.hoisted
		e.hoisted = nil
		initW, err := e.emitStmt(st.Init)
		hoists := e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, err
		}
		outer = append(outer, hoists...)
		outer = append(outer, initW)
	}
	type loopVar struct {
		name, ptr string
		ty, ptrTy any
	}
	lvs := []loopVar{}
	for j, id := range vars {
		obj := e.info.Defs[id]
		ty, err := e.emitType(obj.Type())
		if err != nil {
			return nil, err
		}
		ptrTy := map[string]any{"kind": "pointer", "elem": ty}
		ptr := "$lvp" + itoa(seq) + "_" + itoa(j)
		lvs = append(lvs, loopVar{name: id.Name, ptr: ptr, ty: ty, ptrTy: ptrTy})
		outer = append(outer, map[string]any{
			"stmt":   "assign",
			"define": true,
			"lhs":    []any{map[string]any{"target": "declare", "id": ptr, "type": ptrTy}},
			"rhs":    []any{map[string]any{"expr": "ref", "id": id.Name}},
		})
	}
	firstVar := "$lvf" + itoa(seq)
	if st.Post != nil {
		outer = append(outer, map[string]any{
			"stmt":   "assign",
			"define": true,
			"lhs":    []any{map[string]any{"target": "declare", "id": firstVar, "type": boolTy}},
			"rhs":    []any{map[string]any{"expr": "bool", "value": true}},
		})
	}
	iter := []any{}
	// Fresh per-iteration cells, initialized from the previous iteration's
	// cell; the carrier pointer then addresses THIS iteration's cell.
	for _, v := range lvs {
		iter = append(iter, map[string]any{
			"stmt":   "assign",
			"define": true,
			"lhs":    []any{map[string]any{"target": "declare", "id": v.name, "type": v.ty}},
			"rhs": []any{map[string]any{"expr": "deref",
				"ptr":  map[string]any{"expr": "ident", "name": v.ptr, "type": v.ptrTy},
				"type": v.ty}},
		})
		iter = append(iter, map[string]any{
			"stmt": "assign",
			"lhs":  []any{map[string]any{"target": "var", "id": v.ptr}},
			"rhs":  []any{map[string]any{"expr": "ref", "id": v.name}},
		})
	}
	if st.Post != nil {
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
		iter = append(iter, map[string]any{"stmt": "if",
			"cond": map[string]any{"expr": "ident", "name": firstVar, "type": boolTy},
			"then": map[string]any{"stmt": "assign",
				"lhs": []any{map[string]any{"target": "var", "id": firstVar}},
				"rhs": []any{map[string]any{"expr": "bool", "value": false}}},
			"else": post,
		})
	}
	if st.Cond != nil {
		saved := e.hoisted
		e.hoisted = nil
		cond, err := e.emitExpr(st.Cond)
		condHoists := e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, err
		}
		iter = append(iter, condHoists...)
		iter = append(iter, map[string]any{"stmt": "if", "cond": cond,
			"then": map[string]any{"stmt": "block", "body": []any{}},
			"else": map[string]any{"stmt": "break"}})
	}
	bodyW, err := e.emitBlock(st.Body)
	if err != nil {
		return nil, err
	}
	iter = append(iter, bodyW)
	loop := map[string]any{"stmt": "for",
		"body": map[string]any{"stmt": "block", "body": iter}}
	return map[string]any{"stmt": "block", "body": append(outer, loop)}, nil
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
	// ASSIGN form (`for i, v = range X`): iterate with declared temps and
	// assign the outer lvalues at the top of each iteration (key first,
	// then value — Go's order). Blank targets stay unbound.
	keyName := rangeVarName(rs.Key)
	valName := rangeVarName(rs.Value)
	prefix := []any{}
	if rs.Tok == token.ASSIGN {
		bind := func(outer ast.Expr, temp string) (string, error) {
			id, isIdent := outer.(*ast.Ident)
			if isIdent && id.Name == "_" {
				return "", nil
			}
			// Non-identifier targets evaluate their operands EVERY
			// iteration in Go; the emit-once lowering would freeze one
			// address and hoist the operands' effects out of the loop
			// (pre-merge audit 2026-07-26) — fail closed.
			if !isIdent {
				return "", unsup("range assignment to non-identifier target (operands evaluate per iteration)")
			}
			target, err := e.emitLValue(outer)
			if err != nil {
				return "", err
			}
			ty, err := e.typeOf(outer)
			if err != nil {
				return "", err
			}
			prefix = append(prefix, map[string]any{
				"stmt": "assign", "define": false,
				"lhs": []any{target},
				"rhs": []any{map[string]any{"expr": "ident", "name": temp, "type": ty}},
			})
			return temp, nil
		}
		if rs.Key != nil {
			n, err := bind(rs.Key, "$rangeKey")
			if err != nil {
				return nil, err
			}
			keyName = n
		}
		if rs.Value != nil {
			n, err := bind(rs.Value, "$rangeVal")
			if err != nil {
				return nil, err
			}
			valName = n
		}
	}

	rangeTy := e.goTypeOf(rs.X).Underlying()
	var coll any
	kindFields := map[string]any{}
	if ptr, ok := rangeTy.(*types.Pointer); ok {
		// Range over *[N]T: the pointer evaluates ONCE; the index-only
		// form (and N == 0) never dereferences — a nil pointer iterates
		// fine, N is static — while the value form reads elements through
		// it (nil panics at the first read, which the up-front deref
		// reproduces: nothing observable happens between loop entry and
		// the first element read).
		arr, ok := ptr.Elem().Underlying().(*types.Array)
		if !ok {
			return nil, unsup("range over %s", e.goTypeOf(rs.X))
		}
		pw, err := e.emitExpr(rs.X)
		if err != nil {
			return nil, err
		}
		if valName == "" || arr.Len() == 0 {
			if _, err := e.hoist(pw, e.goTypeOf(rs.X)); err != nil {
				return nil, err
			}
			coll = map[string]any{"expr": "int", "value": itoa(int(arr.Len()))}
			kindFields["kind"] = "int"
			// Ranging an array (through the pointer) indexes with int
			// (spec §For statements) — the static-length int desugar
			// carries that kind explicitly (BUG-043: the decoder fails
			// closed on a kindless range-over-int).
			kindFields["operandType"] = intType("int")
			valName = ""
		} else {
			// Value form: the POINTER binds once; each iteration reads the
			// element THROUGH it, so writes to the array during the loop
			// are observed (an up-front deref snapshotted — pre-merge
			// audit 2026-07-26). A nil pointer panics at the first read.
			arrTy, err := e.emitType(ptr.Elem())
			if err != nil {
				return nil, err
			}
			elemTy, err := e.emitType(arr.Elem())
			if err != nil {
				return nil, err
			}
			pref, err := e.hoist(pw, e.goTypeOf(rs.X))
			if err != nil {
				return nil, err
			}
			coll = pref
			kindFields["kind"] = "array-pointer"
			kindFields["elemType"] = elemTy
			kindFields["arrType"] = arrTy
			kindFields["len"] = arr.Len()
		}
	} else {
		w, err := e.emitExpr(rs.X)
		if err != nil {
			return nil, err
		}
		coll = w
		switch u := rangeTy.(type) {
		case *types.Map:
			kt, err := e.emitType(u.Key())
			if err != nil {
				return nil, err
			}
			vt, err := e.emitType(u.Elem())
			if err != nil {
				return nil, err
			}
			kindFields["kind"] = "map"
			kindFields["keyType"] = kt
			kindFields["valueType"] = vt
		case *types.Slice:
			et, err := e.emitType(u.Elem())
			if err != nil {
				return nil, err
			}
			kindFields["kind"] = "slice"
			kindFields["elemType"] = et
		case *types.Array:
			et, err := e.emitType(u.Elem())
			if err != nil {
				return nil, err
			}
			kindFields["kind"] = "array"
			kindFields["elemType"] = et
		case *types.Basic:
			if u.Info()&types.IsInteger != 0 {
				// Range over an integer: the iteration variable takes the
				// OPERAND's type (spec §For statements), so the wire
				// carries its underlying integer kind — previously no
				// kind was emitted at all and the decoder hard-coded the
				// default int, so arithmetic on the loop variable in the
				// operand's kind went stuck (BUG-043; u is already the
				// operand's Underlying, so defined types resolve here).
				ot, err := e.emitBasic(u)
				if err != nil {
					return nil, err
				}
				kindFields["kind"] = "int"
				kindFields["operandType"] = ot
			} else if u.Info()&types.IsString != 0 {
				kindFields["kind"] = "string"
			} else {
				return nil, unsup("range over %s", u)
			}
		case *types.Chan:
			// Range over a channel (channels arc slice 1): ONE iteration
			// variable (the received value — rs.Key); the decoder desugars
			// to a comma-ok receive loop (non-snapshot: an open, drained
			// channel blocks, which the sequential slice classifies as the
			// deadlocked run — probe p16).
			if valName != "" {
				return nil, unsup("range over channel with a second iteration variable")
			}
			et, err := e.emitType(u.Elem())
			if err != nil {
				return nil, err
			}
			kindFields["kind"] = "chan"
			kindFields["elemType"] = et
		default:
			return nil, unsup("range over %s", e.goTypeOf(rs.X))
		}
	}

	var body any
	blk, err := e.emitBlock(rs.Body)
	if err != nil {
		return nil, err
	}
	body = blk
	if len(prefix) > 0 {
		body = map[string]any{"stmt": "block", "body": append(prefix, body)}
	}
	node := map[string]any{
		"stmt":       "range",
		"keyVar":     nameOrNull(keyName),
		"valVar":     nameOrNull(valName),
		"collection": coll,
		"body":       body,
	}
	for k, v := range kindFields {
		node[k] = v
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
	lvTy, err := e.emitType(e.goTypeOf(lv))
	if err != nil {
		return nil, nil, err
	}
	ref, err := e.hoist(addr, types.NewPointer(e.goTypeOf(lv)))
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
	baseRef, err := e.hoist(baseW, e.goTypeOf(ix.X))
	if err != nil {
		return nil, err
	}
	keyW, err := e.emitExpr(ix.Index)
	if err != nil {
		return nil, err
	}
	// Interface-typed key: box BEFORE the hoist — the temp is declared at
	// the map's key type, so it must hold the boxed key (read and store
	// both compare against boxed stored keys).
	keyW, err = e.wrapInterfaceConversion(mt.Key(), e.goTypeOf(ix.Index), keyW)
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
	// The synthetic 1 (m[k]++/--) takes the VALUE type's UNDERLYING kind:
	// float kinds since the floats slice (F3), integer kinds since BUG-042
	// (m[k]++ over uint8 — or any defined-type — values previously
	// synthesized a default-int 1 and went stuck at the add). ++/-- is
	// go/types-checked numeric, so a non-numeric underlying here is
	// unreachable; the default-int literal below is kept only for that
	// vacuous arm rather than inventing a new failure mode.
	var rhs any = map[string]any{"expr": "int", "value": "1",
		"type": map[string]any{"kind": "int", "int": "int"}}
	if vb, ok := mt.Elem().Underlying().(*types.Basic); ok && vb.Info()&(types.IsFloat|types.IsInteger) != 0 {
		vt, err := e.emitBasic(vb)
		if err != nil {
			return nil, err
		}
		if vb.Info()&types.IsFloat != 0 {
			rhs = map[string]any{"expr": "float", "num": "1", "den": "1", "type": vt}
		} else {
			rhs = map[string]any{"expr": "int", "value": "1", "type": vt}
		}
	}
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
		if mt, ok := e.goTypeOf(ix.X).Underlying().(*types.Map); ok {
			return e.emitMapCompound(ix, mt, op, nil)
		}
	}
	target, read, err := e.emitReadWriteTarget(st.X)
	if err != nil {
		return nil, err
	}
	// Carry the operand type so the synthetic 1 literal takes the operand's
	// integer kind (otherwise uint8-- would mix uint8 with an int literal) —
	// resolved through DEFINED types to the UNDERLYING basic kind, the same
	// resolution emitConstValue applies to defined-typed literals (BUG-042,
	// grossmith seed 559: a {"kind":"named"} wire type made the decoder's
	// literal-kind lookup fall to the default int, so T1(5)++ desugared to
	// an int8 + int add and went stuck). Non-basic underlying (a type
	// parameter outside a stencil) keeps the substitution-aware typeOf path.
	var ty any
	if b, ok := e.goTypeOf(st.X).Underlying().(*types.Basic); ok {
		ty, err = e.emitBasic(b)
	} else {
		ty, err = e.typeOf(st.X)
	}
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "incdec", "op": op, "target": target, "read": read, "type": ty}, nil
}

// ---- expressions ----

// emitSwitch (W2 slice 1, rewritten by the control-flow slice,
// docs/2026-08-04_control-flow-design.md): an expression switch desugars
// to a SELECTION-INDEX form inside a fresh block — the init statement and
// the once-evaluated tag temp scope to the switch; a test chain (nested
// else-blocks, textual order over case values, each case expression's
// hoists spliced immediately before its own test — Go's lazy
// left-to-right evaluation and panic timing) selects a clause index; a
// dispatch chain in SOURCE order (default in position) runs the selected
// clause's body as a SIBLING block, with a fallthrough flag chaining a
// falling-through clause into the next clause's body. Sibling-block
// bodies are Go's actual clause scoping, so fallthrough into/out of
// declaring clauses needs no restriction. Fail-closed residue: type
// switches (interfaces lane, slice 2 of the arc).
// ---- type switches (design note 2026-08-05 D3) ----

// emitTypeSwitch desugars `switch [init;] [v :=] guard.(type) { ... }` to a
// breakable block: the guard evaluated ONCE into a temp, then a first-match
// if-chain in SOURCE order (default in the final else position). Case tests
// are comma-ok asserts (`case nil` compares against the nil interface) —
// effect-free, so eager per-clause test evaluation inside the nested chain
// is observationally silent and only first-match order is load-bearing
// (type-switch-first-match). Clause bodies are their own blocks; the
// per-clause binding (go/types Implicits) is declared at block top — the
// asserted value in a single-type clause, the guard temp otherwise (Go's
// static-type rule). No fallthrough exists in a type switch (spec).
func (e *emitter) emitTypeSwitch(st *ast.TypeSwitchStmt) (any, error) {
	body := []any{}
	if st.Init != nil {
		sub, err := e.emitStmtList([]ast.Stmt{st.Init})
		if err != nil {
			return nil, err
		}
		body = append(body, sub...)
	}
	var guardExpr ast.Expr
	switch a := st.Assign.(type) {
	case *ast.ExprStmt:
		ta, ok := ast.Unparen(a.X).(*ast.TypeAssertExpr)
		if !ok {
			return nil, unsup("type switch guard shape %T", a.X)
		}
		guardExpr = ta.X
	case *ast.AssignStmt:
		if len(a.Rhs) != 1 {
			return nil, unsup("type switch guard arity")
		}
		ta, ok := ast.Unparen(a.Rhs[0]).(*ast.TypeAssertExpr)
		if !ok {
			return nil, unsup("type switch guard shape %T", a.Rhs[0])
		}
		guardExpr = ta.X
	default:
		return nil, unsup("type switch guard statement %T", st.Assign)
	}
	guardTy := e.goTypeOf(guardExpr)
	gty, err := e.emitType(guardTy)
	if err != nil {
		return nil, err
	}
	saved := e.hoisted
	e.hoisted = nil
	guardW, err := e.emitExpr(guardExpr)
	hoists := e.hoisted
	e.hoisted = saved
	if err != nil {
		return nil, err
	}
	seq := e.tmpSeq
	e.tmpSeq++
	tsVar := "$ts" + itoa(seq)
	body = append(body, hoists...)
	body = append(body, map[string]any{
		"stmt": "assign", "define": true,
		"lhs":  []any{map[string]any{"target": "declare", "id": tsVar, "type": gty}},
		"rhs":  []any{guardW},
	})
	tsRef := map[string]any{"expr": "ident", "name": tsVar, "type": gty}

	// Split clauses: SOURCE order for the chain, default kept for the
	// innermost else (Go: default position in source is irrelevant).
	ordered := []*ast.CaseClause{}
	var defaultClause *ast.CaseClause
	for _, raw := range st.Body.List {
		cc, ok := raw.(*ast.CaseClause)
		if !ok {
			return nil, unsup("type switch body statement %T", raw)
		}
		if cc.List == nil {
			defaultClause = cc
			continue
		}
		ordered = append(ordered, cc)
	}
	var chain any
	if defaultClause != nil {
		b, err := e.typeSwitchClauseBody(defaultClause, tsRef)
		if err != nil {
			return nil, err
		}
		chain = b
	}
	for k := len(ordered) - 1; k >= 0; k-- {
		cc := ordered[k]
		pre := []any{}
		var cond any
		var boundVal any
		if len(cc.List) == 1 {
			c1, bv, p1, err := e.typeSwitchTest(cc.List[0], tsRef, gty)
			if err != nil {
				return nil, err
			}
			cond, boundVal, pre = c1, bv, p1
		} else {
			for _, texpr := range cc.List {
				c1, _, p1, err := e.typeSwitchTest(texpr, tsRef, gty)
				if err != nil {
					return nil, err
				}
				pre = append(pre, p1...)
				if cond == nil {
					cond = c1
				} else {
					cond = map[string]any{"expr": "binary", "op": "||", "x": cond, "y": c1}
				}
			}
			boundVal = nil // multi-type clause binds the guard value
		}
		if boundVal == nil {
			boundVal = tsRef
		}
		b, err := e.typeSwitchClauseBody(cc, boundVal)
		if err != nil {
			return nil, err
		}
		ifNode := map[string]any{"stmt": "if", "cond": cond, "then": b}
		if chain != nil {
			ifNode["else"] = chain
		}
		chain = map[string]any{"stmt": "block", "body": append(pre, ifNode)}
	}
	if chain != nil {
		body = append(body, chain)
	}
	return map[string]any{"stmt": "breakable",
		"body": map[string]any{"stmt": "block", "body": body}}, nil
}

// typeSwitchTest emits one case-type test against the guard temp: a
// comma-ok assert into fresh temps (cond = the ok temp, boundVal = the
// value temp), or a nil-interface comparison for `case nil` (cond only,
// boundVal = nil meaning "bind the guard value").
func (e *emitter) typeSwitchTest(texpr ast.Expr, tsRef any, gty any) (any, any, []any, error) {
	if tv, ok := e.info.Types[texpr]; ok && tv.IsNil() {
		// Bare (untyped) nil: the nil interface IS the raw nil value; a
		// typed nil BOX correctly compares unequal (type-switch-typed-nil).
		cond := map[string]any{"expr": "binary", "op": "==",
			"x":           tsRef,
			"y":           map[string]any{"expr": "nil"},
			"operandType": gty}
		return cond, nil, nil, nil
	}
	target := e.goTypeOf(texpr)
	tw, err := e.emitType(target)
	if err != nil {
		return nil, nil, nil, err
	}
	seq := e.tmpSeq
	e.tmpSeq++
	vVar := "$tsv" + itoa(seq)
	okVar := "$tso" + itoa(seq)
	boolTy := map[string]any{"kind": "bool"}
	pre := []any{map[string]any{
		"stmt":       "type-assert",
		"target":     map[string]any{"target": "declare", "id": vVar, "type": tw},
		"okTarget":   map[string]any{"target": "declare", "id": okVar, "type": boolTy},
		"expr":       tsRef,
		"targetType": tw,
	}}
	cond := map[string]any{"expr": "ident", "name": okVar, "type": boolTy}
	boundVal := map[string]any{"expr": "ident", "name": vVar, "type": tw}
	return cond, boundVal, pre, nil
}

// typeSwitchClauseBody emits a clause body block, prefixed by the clause's
// implicit binding (go/types Implicits) initialized to boundVal.
func (e *emitter) typeSwitchClauseBody(cc *ast.CaseClause, boundVal any) (any, error) {
	stmts := []any{}
	if obj, ok := e.info.Implicits[cc]; ok {
		if v, isVar := obj.(*types.Var); isVar {
			vty, err := e.emitType(v.Type())
			if err != nil {
				return nil, err
			}
			stmts = append(stmts, map[string]any{
				"stmt": "assign", "define": true,
				"lhs":  []any{map[string]any{"target": "declare", "id": v.Name(), "type": vty}},
				"rhs":  []any{boundVal},
			})
		}
	}
	bodyStmts, err := e.emitStmtList(cc.Body)
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "block", "body": append(stmts, bodyStmts...)}, nil
}

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
	type swCase struct {
		clause int
		expr   ast.Expr
	}
	type swClause struct {
		isDefault bool
		stmts     []any
		fallsThru bool
	}
	clauses := []swClause{}
	cases := []swCase{} // case VALUES in textual order (default has none)
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
		cbody, err := e.emitStmtList(list)
		if err != nil {
			return nil, err
		}
		idx := len(clauses)
		cl := swClause{isDefault: cc.List == nil, stmts: cbody, fallsThru: fallsThru}
		for _, ce := range cc.List {
			cases = append(cases, swCase{clause: idx, expr: ce})
		}
		clauses = append(clauses, cl)
	}
	seq := e.tmpSeq
	e.tmpSeq++
	idxVar := "$swi" + itoa(seq)
	fallVar := "$swf" + itoa(seq)
	intTy := map[string]any{"kind": "int", "int": "int"}
	boolTy := map[string]any{"kind": "bool"}
	intLit := func(v int) any {
		return map[string]any{"expr": "int", "value": itoa(v), "type": intTy}
	}
	// The selected clause index: the default clause's if nothing matches,
	// or the no-body sentinel len(clauses).
	defaultIdx := len(clauses)
	for i, cl := range clauses {
		if cl.isDefault {
			defaultIdx = i
		}
	}
	body = append(body, map[string]any{
		"stmt":   "assign",
		"define": true,
		"lhs":    []any{map[string]any{"target": "declare", "id": idxVar, "type": intTy}},
		"rhs":    []any{intLit(defaultIdx)},
	})
	// Test chain, built innermost-first: each case value's hoists run in
	// its own block, only if every earlier test failed.
	var chain any
	for k := len(cases) - 1; k >= 0; k-- {
		saved := e.hoisted
		e.hoisted = nil
		cw, err := e.emitExpr(cases[k].expr)
		hoists := e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, err
		}
		var cond any
		if st.Tag == nil {
			cond = cw
		} else {
			// Switch-case slot of an interface-tagged switch: box a
			// non-interface case value into the tag's interface type —
			// the same spec rule as emitBinary's mixed comparison
			// (BUG-017, arc-final audit F4). The reverse shape
			// (non-interface tag, interface case value) boxes the TAG
			// reference per-case and compares at the case's type.
			condTagRef := tagRef
			condTagTy := tagTy
			tagGo := e.applySubst(e.goTypeOf(st.Tag))
			caseGo := e.applySubst(e.goTypeOf(cases[k].expr))
			tagIsIface := tagGo != nil && types.IsInterface(tagGo)
			caseIsIface := caseGo != nil && types.IsInterface(caseGo)
			if tagIsIface && !caseIsIface {
				if cw, err = e.wrapInterfaceConversion(tagGo, e.goTypeOf(cases[k].expr), cw); err != nil {
					return nil, err
				}
			} else if caseIsIface && !tagIsIface {
				if condTagRef, err = e.wrapInterfaceConversion(caseGo, e.goTypeOf(st.Tag), condTagRef); err != nil {
					return nil, err
				}
				cty, err := e.typeOf(cases[k].expr)
				if err != nil {
					return nil, err
				}
				condTagTy = cty
			}
			cond = map[string]any{"expr": "binary", "op": "==", "x": condTagRef, "y": cw, "operandType": condTagTy}
		}
		ifNode := map[string]any{"stmt": "if", "cond": cond,
			"then": map[string]any{
				"stmt": "assign",
				"lhs":  []any{map[string]any{"target": "var", "id": idxVar}},
				"rhs":  []any{intLit(cases[k].clause)},
			}}
		if chain != nil {
			ifNode["else"] = chain
		}
		chain = map[string]any{"stmt": "block",
			"body": append(append([]any{}, hoists...), ifNode)}
	}
	if chain != nil {
		body = append(body, chain)
	}
	// Dispatch chain, source order. `$swf` chains fallthrough: a clause
	// ending in `fallthrough` completes normally and arms the next
	// clause's guard; a body exiting via break/return/panic never reaches
	// the arming statement — Go's rule.
	body = append(body, map[string]any{
		"stmt":   "assign",
		"define": true,
		"lhs":    []any{map[string]any{"target": "declare", "id": fallVar, "type": boolTy}},
		"rhs":    []any{map[string]any{"expr": "bool", "value": false}},
	})
	for i, cl := range clauses {
		if cl.fallsThru && i+1 >= len(clauses) {
			// go/types rejects this upstream; defensive fail-closed.
			return nil, unsup("fallthrough in final switch clause")
		}
		guard := map[string]any{"expr": "binary", "op": "||",
			"x": map[string]any{"expr": "ident", "name": fallVar, "type": boolTy},
			"y": map[string]any{"expr": "binary", "op": "==",
				"x":           map[string]any{"expr": "ident", "name": idxVar, "type": intTy},
				"y":           intLit(i),
				"operandType": intTy}}
		thenStmts := []any{
			map[string]any{
				"stmt": "assign",
				"lhs":  []any{map[string]any{"target": "var", "id": fallVar}},
				"rhs":  []any{map[string]any{"expr": "bool", "value": false}},
			},
			// The clause body is a SIBLING block (Go's clause scoping).
			map[string]any{"stmt": "block", "body": cl.stmts},
		}
		if cl.fallsThru {
			thenStmts = append(thenStmts, map[string]any{
				"stmt": "assign",
				"lhs":  []any{map[string]any{"target": "var", "id": fallVar}},
				"rhs":  []any{map[string]any{"expr": "bool", "value": true}},
			})
		}
		body = append(body, map[string]any{"stmt": "if", "cond": guard,
			"then": map[string]any{"stmt": "block", "body": thenStmts}})
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
		if tv, ok := e.typesEntry(x); ok && tv.Value != nil {
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
		// A generic INSTANTIATION `f[int]` parses as an index expression;
		// in VALUE position it is a func value of the stencil (partial
		// source instantiations like `hoiFirst[int]` still carry the FULL
		// inference-completed argument list in Instances). An index whose
		// Index is a type but whose base is not a generic function fails
		// closed (treating it as indexing would emit the type argument as
		// a variable read — stuck at runtime instead of a boundary
		// refusal).
		if tv, ok := e.info.Types[ex.Index]; ok && tv.IsType() {
			if node, err, handled := e.genericFuncValue(ex.X); handled {
				return node, err
			}
			return nil, unsup("generic instantiation %s", e.fset.Position(ex.Pos()))
		}
		return e.emitIndex(ex)
	case *ast.IndexListExpr:
		// Multi-argument explicit instantiation `f[a, b]` in value
		// position; nothing else parses as an IndexListExpr.
		if node, err, handled := e.genericFuncValue(ex.X); handled {
			return node, err
		}
		return nil, unsup("generic instantiation %s", e.fset.Position(ex.Pos()))
	case *ast.StarExpr:
		return e.emitStar(ex)
	case *ast.SliceExpr:
		return e.emitSliceExpr(ex)
	case *ast.FuncLit:
		return e.emitFuncLit(ex)
	case *ast.TypeAssertExpr:
		// Single-result panicking form `x.(T)`. The comma-ok form is a
		// dedicated statement (emitAssign); a comma-ok assert reaching
		// expression position (its type is a tuple) is an unmodeled shape.
		// `x.(type)` (Type == nil) only occurs under a type switch, which
		// fails closed at the statement level.
		if ex.Type == nil {
			return nil, unsup("type switch guard in expression position")
		}
		if _, isTup := e.goTypeOf(ex).(*types.Tuple); isTup {
			return nil, unsup("type assert form outside a 2-target assignment (interfaces campaign, deferred)")
		}
		operand, err := e.emitExpr(ex.X)
		if err != nil {
			return nil, err
		}
		target, err := e.emitType(e.goTypeOf(ex.Type))
		if err != nil {
			return nil, err
		}
		// The operand's STATIC interface type: Go's failed-assert message
		// names it (`interface conversion: main.I is main.T, not *main.T`),
		// and it is NOT recoverable from the runtime value (pre-merge audit
		// 2026-07-31, finding 8). Only the single-result form panics, so only
		// this form carries it.
		source, err := e.emitType(e.goTypeOf(ex.X))
		if err != nil {
			return nil, err
		}
		return map[string]any{"expr": "type-assert", "operand": operand,
			"target": target, "source": source}, nil
	default:
		return nil, unsup("expression %T at %s", x, e.fset.Position(x.Pos()))
	}
}

func (e *emitter) emitSliceExpr(se *ast.SliceExpr) (any, error) {
	// Array bases slice through their address; slice/string bases by value.
	var base any
	var err error
	if _, isArray := e.goTypeOf(se.X).Underlying().(*types.Array); isArray {
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

// qualifiedTypeName renders a declared type's wire name PACKAGE-QUALIFIED
// ("main.sliceError") — Go renders panic messages qualified, and the TypeId
// is what GoCore decides dynamic-type IDENTITY on. Predeclared (universe)
// types like `error` have no package and stay bare.
//
// The qualifier is the package NAME, which is NOT Go's identity: Go keys
// type identity on the IMPORT PATH, so `html/template.Template` and
// `text/template.Template` — both in a package named `template` — are
// distinct types that this prefix cannot tell apart (pre-merge audit
// 2026-07-31, findings 4/7; the assert between them answered `true` where
// Go answers `false`). Widening the key to the import path is the real
// fix and is scoped in docs/2026-07-30_quorum-extern-policy.md; until
// then every qualifier is RECORDED here and
// `checkPackageNameCollisions` fails the export CLOSED when two distinct
// import paths would produce the same prefix.
func (e *emitter) qualifiedTypeName(obj *types.TypeName) string {
	pkg := obj.Pkg()
	if pkg == nil {
		return obj.Name()
	}
	if e.qualPkgPaths == nil {
		e.qualPkgPaths = map[string][]string{}
	}
	name := pkg.Name()
	paths := e.qualPkgPaths[name]
	seen := false
	for _, p := range paths {
		if p == pkg.Path() {
			seen = true
			break
		}
	}
	if !seen {
		e.qualPkgPaths[name] = append(paths, pkg.Path())
	}
	base := name + "." + obj.Name()
	// A type DECLARED INSIDE a generic function (its scope is not the
	// package scope) is named by gc with the ENCLOSING INSTANTIATION's
	// type arguments — probe-verified go1.26.5: reflect.Name() =
	// "box[int]", String() = "main.box[int]" — so the TypeId
	// parameterizes the same way (arc-final audit F3, 2026-08-06;
	// BUG-018: the bare key aliased instantiations, reporting wrong
	// dynamic names at one instantiation and refusing legal Go at two).
	// Rendering failures record substErr (fail closed at the stencil
	// boundary, like applySubst) and keep the bare name for the refusal
	// message.
	if e.curTargs != nil && obj.Parent() != pkg.Scope() {
		rendered := make([]string, len(e.curTargs))
		ok := true
		for i, t := range e.curTargs {
			r, err := e.renderTypeArg(t)
			if err != nil {
				if e.substErr == nil {
					e.substErr = err
				}
				ok = false
				break
			}
			rendered[i] = r
		}
		if ok {
			base += "[" + strings.Join(rendered, ",") + "]"
		}
	}
	return base
}

// checkPackageNameCollisions fails the export when two DISTINCT import
// paths contributed type names under the same package-name qualifier: the
// wire's TypeIds would collide and GoCore would decide two unrelated Go
// types identical. Fail closed at the one boundary that constructs the key
// (CLAUDE.md: "every mangling strip happens at exactly one boundary
// constructor and collision-checks").
func (e *emitter) checkPackageNameCollisions() error {
	names := make([]string, 0, len(e.qualPkgPaths))
	for name := range e.qualPkgPaths {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		paths := e.qualPkgPaths[name]
		if len(paths) > 1 {
			sorted := append([]string(nil), paths...)
			sort.Strings(sorted)
			return unsup("package-name collision in TypeId keys: %q is the package name of %v — "+
				"Go keys type identity on the import PATH, so these declare DISTINCT types that "+
				"the name-qualified wire key cannot tell apart", name, sorted)
		}
	}
	return nil
}

// namedTypeName returns the qualified declared name of a (possibly
// pointer-wrapped) named type, for use as a GoCore struct TypeId. It is
// substitution- and instantiation-aware (mono.go): inside a stencil the
// name is resolved at the current instantiation, and an instantiated
// generic type names by its mangled key (which also enqueues its TypeDef
// stencil — every TypeId the wire mentions must be declared).
func (e *emitter) namedTypeName(t types.Type) (string, bool) {
	// Aliases are identity-transparent (G4): the NAME belongs to the
	// aliased type, never the alias.
	t = types.Unalias(e.applySubst(t))
	if named, ok := t.(*types.Named); ok {
		if named.TypeArgs().Len() > 0 {
			key, err := e.instTypeIdForWire(named)
			if err != nil {
				// Callers refuse on false; the loud per-key reason is
				// re-raised when the type itself reaches emitType.
				return "", false
			}
			return key, true
		}
		return e.qualifiedTypeName(named.Obj()), true
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
	if _, alreadyPtr := e.goTypeOf(sel.X).Underlying().(*types.Pointer); alreadyPtr {
		return e.emitExpr(sel.X)
	}
	return e.emitAddressOf(sel.X)
}

// ---- promotion (embedded fields; design note 2026-08-05 D1) ----
//
// go/types resolves every promoted selection to a field/method path through
// embedded fields (`Selection.Index()`); the frontend FLATTENS that path at
// emission, so GoCore's field access and method table stay single-hop/flat.

// fieldPathValue walks `index` (each entry a field index, embedded hops
// included) from a VALUE node of type t, emitting field-get hops and
// auto-dereferencing pointer hops (a nil embedded pointer panics at the
// deref — Go's promoted-access panic). Returns the final field's value node
// and type.
func (e *emitter) fieldPathValue(node any, t types.Type, index []int) (any, types.Type, error) {
	for _, i := range index {
		base := t
		if ptr, ok := base.Underlying().(*types.Pointer); ok {
			elem := ptr.Elem()
			elemTy, err := e.emitType(elem)
			if err != nil {
				return nil, nil, err
			}
			node = map[string]any{"expr": "deref", "ptr": node, "type": elemTy}
			base = elem
		}
		st, ok := base.Underlying().(*types.Struct)
		if !ok {
			return nil, nil, unsup("promoted field path through non-struct type %s", base)
		}
		name, ok := e.namedTypeName(base)
		if !ok {
			return nil, nil, unsup("field selector on anonymous struct type %s", base)
		}
		f := st.Field(i)
		node = map[string]any{"expr": "field-get", "recv": node, "typeId": name, "field": f.Name()}
		t = f.Type()
	}
	return node, t, nil
}

// fieldPathAddr walks `index` from expression x, emitting the ADDRESS of
// the final field: field-addr hops from the addressable root (or the
// pointer value when the base/hop is already a pointer).
func (e *emitter) fieldPathAddr(x ast.Expr, index []int) (any, types.Type, error) {
	t := e.goTypeOf(x)
	var node any
	var err error
	var cur types.Type
	if ptr, ok := t.Underlying().(*types.Pointer); ok {
		node, err = e.emitExpr(x)
		cur = ptr.Elem()
	} else {
		node, err = e.emitAddressOf(x)
		cur = t
	}
	if err != nil {
		return nil, nil, err
	}
	return e.fieldPathAddrFrom(node, cur, index)
}

// fieldPathAddrFrom is fieldPathAddr's node-based core (also used by the
// synthesized promotion wrappers, whose root is the $recv parameter). Loop
// invariant: node's value is a pointer to a cell of (non-pointer) type cur.
func (e *emitter) fieldPathAddrFrom(node any, cur types.Type, index []int) (any, types.Type, error) {
	for k, i := range index {
		st, ok := cur.Underlying().(*types.Struct)
		if !ok {
			return nil, nil, unsup("promoted field path through non-struct type %s", cur)
		}
		name, ok := e.namedTypeName(cur)
		if !ok {
			return nil, nil, unsup("field address on anonymous struct type %s", cur)
		}
		f := st.Field(i)
		node = map[string]any{"expr": "field-addr", "base": node, "typeId": name, "field": f.Name()}
		cur = f.Type()
		if ptr, ok := cur.Underlying().(*types.Pointer); ok && k+1 < len(index) {
			// An embedded POINTER hop: the pointer's VALUE is the address
			// of the next level (loading a nil one panics — Go).
			fTy, err := e.emitType(cur)
			if err != nil {
				return nil, nil, err
			}
			node = map[string]any{"expr": "deref", "ptr": node, "type": fTy}
			cur = ptr.Elem()
		}
	}
	return node, cur, nil
}

// promotedFieldIndex returns the go/types selection path when sel is a
// PROMOTED field selection (an embedded hop exists), else nil.
func (e *emitter) promotedFieldIndex(sel *ast.SelectorExpr) []int {
	if seln, ok := e.info.Selections[sel]; ok && seln.Kind() == types.FieldVal && len(seln.Index()) > 1 {
		return seln.Index()
	}
	return nil
}

// synthesizePromotionWrappers builds one forwarding method per PROMOTED
// method-set entry (multi-hop Selection.Index) of every declared named
// struct type: receiver `T` when the method is in T's own method set
// (value promotion), `*T` when it is only in *T's (pointer-receiver
// promotion through value embedding — Go's method-set asymmetry). The
// machine's method table is flat; these wrappers are what make it
// COMPLETE, which is the wire contract that lets interface satisfaction
// answer a definite "no" on embedded-field types (design note D2 — the
// retired BUG-007 fail-closure). A wrapper that cannot be emitted fails
// the whole export, the standing policy for methods.
func (e *emitter) synthesizePromotionWrappers() ([]any, error) {
	out := []any{}
	seen := map[string]bool{}
	for _, named := range e.namedStructTypes {
		// Instantiated structs (mono.go) name by their mangled key; the
		// substitution-aware namedTypeName covers both spellings.
		tName, okName := e.namedTypeName(named)
		if !okName {
			tName = e.qualifiedTypeName(named.Obj())
		}
		valSet := types.NewMethodSet(named)
		ptrSet := types.NewMethodSet(types.NewPointer(named))
		for i := 0; i < ptrSet.Len(); i++ {
			msel := ptrSet.At(i)
			if len(msel.Index()) <= 1 {
				continue // declared directly on T, not promoted
			}
			mfn, ok := msel.Obj().(*types.Func)
			if !ok {
				return nil, unsup("promoted method-set entry %s is not a func", msel.Obj().Name())
			}
			key := tName + "." + mfn.Name()
			if seen[key] {
				continue
			}
			seen[key] = true
			useSel := msel
			recvIsPtr := true
			if vs := valSet.Lookup(mfn.Pkg(), mfn.Name()); vs != nil {
				useSel = vs
				recvIsPtr = false
			}
			w, err := e.synthesizeWrapper(named, tName, useSel, recvIsPtr)
			if err != nil {
				return nil, err
			}
			out = append(out, w)
		}
	}
	return out, nil
}

// synthesizeWrapper emits one forwarding wrapper method: body = walk the
// embedded hops from $recv, call the original method (or dispatch on the
// embedded interface field's value), return its results.
func (e *emitter) synthesizeWrapper(named *types.Named, tName string, msel *types.Selection, recvIsPtr bool) (map[string]any, error) {
	mfn := msel.Obj().(*types.Func)
	sig := mfn.Type().(*types.Signature)
	index := msel.Index()
	hops := index[:len(index)-1]

	valueTy, err := e.emitType(named)
	if err != nil {
		return nil, err
	}
	recvTy := valueTy
	var rootT types.Type = named
	if recvIsPtr {
		recvTy = map[string]any{"kind": "pointer", "elem": valueTy}
		rootT = types.NewPointer(named)
	}
	recvIdent := map[string]any{"expr": "ident", "name": "$recv", "type": recvTy}

	params := []any{}
	argIdents := []any{}
	for i := 0; i < sig.Params().Len(); i++ {
		pt, err := e.emitType(sig.Params().At(i).Type())
		if err != nil {
			return nil, err
		}
		id := "$p" + itoa(i)
		params = append(params, map[string]any{"id": id, "type": pt})
		argIdents = append(argIdents, map[string]any{"expr": "ident", "name": id, "type": pt})
	}
	results := []any{}
	resultTypes := []any{}
	for i := 0; i < sig.Results().Len(); i++ {
		rt, err := e.emitType(sig.Results().At(i).Type())
		if err != nil {
			return nil, err
		}
		results = append(results, map[string]any{"id": syntheticResult(i), "type": rt})
		resultTypes = append(resultTypes, rt)
	}

	origRecv := sig.Recv().Type()
	var innerFunc string
	var innerRecvArg any
	if origIface, isIface := origRecv.Underlying().(*types.Interface); isIface {
		// Promoted from an embedded INTERFACE field: forward as dynamic
		// dispatch on the field value (nil field panics at dispatch — Go's
		// nil-interface method call).
		node, ft, err := e.fieldPathValue(recvIdent, rootT, hops)
		if err != nil {
			return nil, err
		}
		ifaceName, ok := e.namedTypeName(ft)
		if !ok {
			return nil, unsup("promotion from anonymous interface field in %s", tName)
		}
		e.noteInterface(ifaceName, origIface)
		e.noteCalledIfaceMethod(ifaceName+"."+mfn.Name(), calledIfaceMethod{
			ifaceName: ifaceName, method: mfn.Name(), sig: sig,
			subst: e.curSubst,
		})
		innerFunc = ifaceName + "." + mfn.Name()
		innerRecvArg = node
	} else {
		defType := origRecv
		innerPtr := false
		if ptr, ok := origRecv.(*types.Pointer); ok {
			defType = ptr.Elem()
			innerPtr = true
		}
		defName, ok := e.namedTypeName(defType)
		if !ok {
			return nil, unsup("promoted method on anonymous type %s", defType)
		}
		innerFunc = defName + "." + mfn.Name()
		ft, err := hopFinalType(rootT, hops)
		if err != nil {
			return nil, err
		}
		ftPtr, ftIsPtr := ft.Underlying().(*types.Pointer)
		if innerPtr && !ftIsPtr {
			// The field's ADDRESS. Two legal sources (audit F2, 2026-08-05
			// — the first cut wrongly claimed only *T's method set can hold
			// this shape and refused, killing whole exports): a POINTER
			// wrapper receiver supplies the root address; or the hop chain
			// crosses an embedded POINTER field, which puts the method in
			// the VALUE method set too (spec: embedding *T contributes
			// both receiver kinds) and whose pointer VALUE supplies the
			// address mid-chain.
			if recvIsPtr {
				node, _, err := e.fieldPathAddrFrom(recvIdent, named, hops)
				if err != nil {
					return nil, err
				}
				innerRecvArg = node
			} else {
				node, err := e.valueRootedFieldAddr(recvIdent, named, hops)
				if err != nil {
					return nil, err
				}
				innerRecvArg = node
			}
		} else {
			node, _, err := e.fieldPathValue(recvIdent, rootT, hops)
			if err != nil {
				return nil, err
			}
			if !innerPtr && ftIsPtr {
				elemTy, err := e.emitType(ftPtr.Elem())
				if err != nil {
					return nil, err
				}
				node = map[string]any{"expr": "deref", "ptr": node, "type": elemTy}
			}
			innerRecvArg = node
		}
	}

	callNode := map[string]any{"expr": "call", "func": innerFunc,
		"args": append([]any{innerRecvArg}, argIdents...), "resultTypes": resultTypes}
	bodyStmts := []any{}
	if len(results) == 0 {
		bodyStmts = append(bodyStmts,
			map[string]any{"stmt": "expr", "expr": callNode},
			map[string]any{"stmt": "return", "results": []any{}})
	} else {
		lhs := []any{}
		rets := []any{}
		for i := range results {
			id := "$w" + itoa(i)
			rm := results[i].(map[string]any)
			lhs = append(lhs, map[string]any{"target": "declare", "id": id, "type": rm["type"]})
			rets = append(rets, map[string]any{"expr": "ident", "name": id, "type": rm["type"]})
		}
		bodyStmts = append(bodyStmts,
			map[string]any{"stmt": "assign", "define": true, "lhs": lhs, "rhs": []any{callNode}},
			map[string]any{"stmt": "return", "results": rets})
	}
	return map[string]any{
		"name":     mfn.Name(),
		"recvType": tName,
		"recv":     map[string]any{"id": "$recv", "type": recvTy},
		"params":   params,
		"results":  results,
		"variadic": sig.Variadic(),
		// Declared schema addition (arc-final audit F1 / BUG-015,
		// 2026-08-06): a SYNTHESIZED promotion wrapper is marked so the
		// machine's recover walk can treat its frame as transparent —
		// gc's abi.FuncIDWrapper, verbatim ("there must be exactly one
		// non-wrapper frame between gopanic and gorecover",
		// runtime/panic.go). Only this constructor emits it.
		"wrapper": true,
		"body":    map[string]any{"stmt": "block", "body": bodyStmts},
	}, nil
}

// ifaceWireName returns the wire TypeId for an interface-typed static
// type: the qualified name for a named interface, the canonical structural
// rendering for an anonymous one (which it registers for the declaration
// pass — same naming as emitType's anonymous-interface arm).
func (e *emitter) ifaceWireName(t types.Type) (string, bool) {
	// Aliases materialize globally under gotypesalias=1 (G4), so the
	// STRUCTURAL fallback must unalias before asserting — a non-generic
	// `type R = interface{ M() int }` static type is a *types.Alias, and
	// the raw assertion returned not-found, quarantining every dispatch
	// through it (audit response M2; pinned by
	// interfaces/anonymous-alias-dispatch).
	t = types.Unalias(t)
	if name, ok := e.namedTypeName(t); ok {
		return name, true
	}
	if iface, ok := t.(*types.Interface); ok && iface.IsMethodSet() {
		if iface.Empty() {
			return emptyInterfaceName, true
		}
		name := types.TypeString(iface, func(p *types.Package) string { return p.Name() })
		e.noteInterface(name, iface)
		return name, true
	}
	return "", false
}

// valueRootedFieldAddr emits the ADDRESS of the field at `hops` starting
// from a VALUE node of (non-pointer) type t — legal exactly when the
// chain crosses an embedded POINTER hop, whose pointer VALUE is a heap
// address the rest of the chain roots at (Go's method-set rule: embedding
// *T contributes pointer-receiver methods to the VALUE method set, audit
// F2). Value-mode field-gets to the first pointer hop, address-mode
// beyond it; copying the value prefix is unobservable — it is only read
// to reach the pointer, and the address obtained is the shared heap cell.
func (e *emitter) valueRootedFieldAddr(node any, t types.Type, hops []int) (any, error) {
	for i, idx := range hops {
		st, ok := t.Underlying().(*types.Struct)
		if !ok {
			return nil, unsup("promoted field path through non-struct type %s", t)
		}
		name, ok := e.namedTypeName(t)
		if !ok {
			return nil, unsup("field selector on anonymous struct type %s", t)
		}
		f := st.Field(idx)
		node = map[string]any{"expr": "field-get", "recv": node, "typeId": name, "field": f.Name()}
		t = f.Type()
		if ptr, isPtr := t.Underlying().(*types.Pointer); isPtr {
			addr, _, err := e.fieldPathAddrFrom(node, ptr.Elem(), hops[i+1:])
			return addr, err
		}
	}
	return nil, unsup("pointer-receiver promotion from a value receiver without a pointer hop (not in the value method set)")
}

// hopFinalType statically walks the embedded-hop types (no emission): the
// type of the field reached by `hops` from t.
func hopFinalType(t types.Type, hops []int) (types.Type, error) {
	for _, i := range hops {
		if ptr, ok := t.Underlying().(*types.Pointer); ok {
			t = ptr.Elem()
		}
		st, ok := t.Underlying().(*types.Struct)
		if !ok {
			return nil, unsup("promoted hop through non-struct type %s", t)
		}
		t = st.Field(i).Type()
	}
	return t, nil
}

// promotedReceiverArg emits the receiver operand for a (possibly promoted)
// concrete-receiver method call or method value. With no hops it is
// methodReceiverArg; with hops the receiver is adjusted through the
// embedded path AT THIS MOMENT (design note D1.2 — the faithful evaluation
// order for calls, and the faithful capture moment for method values):
//   pointer receiver reached at a pointer field  -> the field's VALUE
//   pointer receiver reached at a value field    -> the field's ADDRESS
//   value receiver reached at a pointer field    -> deref of the VALUE
//   value receiver reached at a value field      -> the field's VALUE
func (e *emitter) promotedReceiverArg(sel *ast.SelectorExpr, hops []int, pointerRecv bool) (any, error) {
	if len(hops) == 0 {
		return e.methodReceiverArg(sel, pointerRecv)
	}
	ft, err := hopFinalType(e.goTypeOf(sel.X), hops)
	if err != nil {
		return nil, err
	}
	ftPtr, ftIsPtr := ft.Underlying().(*types.Pointer)
	if pointerRecv && !ftIsPtr {
		node, _, err := e.fieldPathAddr(sel.X, hops)
		return node, err
	}
	base, err := e.emitExpr(sel.X)
	if err != nil {
		return nil, err
	}
	node, _, err := e.fieldPathValue(base, e.goTypeOf(sel.X), hops)
	if err != nil {
		return nil, err
	}
	if !pointerRecv && ftIsPtr {
		elemTy, err := e.emitType(ftPtr.Elem())
		if err != nil {
			return nil, err
		}
		node = map[string]any{"expr": "deref", "ptr": node, "type": elemTy}
	}
	return node, nil
}


// importedTypeDecls emits, for every IMPORTED concrete named type whose
// identity reached the wire and whose EXPORTED method set is fully
// emittable, an `unsupported`-marker TypeDef (existence only) plus
// signature-carrying method STUBS (design note D5) — so interface
// satisfaction gets a real method set to answer from (BUG-009's
// polarity) while structural use and CALLS keep failing closed. A type
// with any un-emittable exported signature is skipped WHOLE (no marker,
// no stubs): the machine then keeps refusing satisfaction for it, never
// answering from a partial set. Unexported methods are skipped — the
// wire cannot express cross-package unexported method identity — and the
// machine fails closed when an UNEXPORTED requirement would decide
// satisfaction against a marker type (Ops.firstUnsatisfiedMethod?).
// Runs to fixpoint: a stub's signature may itself mention fresh imported
// types.
func (e *emitter) importedTypeDecls() ([]any, []any) {
	tds := []any{}
	stubs := []any{}
	done := map[string]bool{}
	for {
		pending := []string{}
		for n := range e.importedNamed {
			if !done[n] {
				pending = append(pending, n)
			}
		}
		if len(pending) == 0 {
			return tds, stubs
		}
		sort.Strings(pending)
		for _, qname := range pending {
			done[qname] = true
			ms, ok := e.importedMethodStubs(qname, e.importedNamed[qname])
			if !ok {
				continue
			}
			tds = append(tds, map[string]any{
				"name": qname,
				"def":  map[string]any{"kind": "unsupported", "feature": "imported named type " + qname},
			})
			stubs = append(stubs, ms...)
		}
	}
}

func (e *emitter) importedMethodStubs(qname string, named *types.Named) ([]any, bool) {
	valSet := types.NewMethodSet(named)
	ptrSet := types.NewMethodSet(types.NewPointer(named))
	out := []any{}
	for i := 0; i < ptrSet.Len(); i++ {
		mfn, ok := ptrSet.At(i).Obj().(*types.Func)
		if !ok {
			return nil, false
		}
		if !mfn.Exported() {
			continue
		}
		sig := mfn.Type().(*types.Signature)
		valueTy, err := e.emitType(named)
		if err != nil {
			return nil, false
		}
		recvTy := any(valueTy)
		if valSet.Lookup(mfn.Pkg(), mfn.Name()) == nil {
			recvTy = map[string]any{"kind": "pointer", "elem": valueTy}
		}
		params, err := e.emitParams(sig.Params())
		if err != nil {
			return nil, false
		}
		results, err := e.emitResults(sig.Results())
		if err != nil {
			return nil, false
		}
		out = append(out, map[string]any{
			"name":     mfn.Name(),
			"recvType": qname,
			"recv":     map[string]any{"id": "$recv", "type": recvTy},
			"params":   params,
			"results":  results,
			"variadic": sig.Variadic(),
			"unsupported": "imported method " + qname + "." + mfn.Name() +
				" (declaration-only stub: satisfaction answers, calls fail closed)",
		})
	}
	return out, true
}

// stringLitNode emits a string literal wire node (the machine's GoString
// byte representation).
func stringLitNode(s string) map[string]any {
	bytes := []byte(s)
	vals := make([]any, len(bytes))
	for i, b := range bytes {
		vals[i] = int64(b)
	}
	return map[string]any{"expr": "string", "bytes": vals}
}

func (e *emitter) fieldBase(sel *ast.SelectorExpr) (any, string, error) {
	recvType := e.goTypeOf(sel.X)
	base, err := e.emitExpr(sel.X)
	if err != nil {
		return nil, "", err
	}
	if ptr, ok := recvType.Underlying().(*types.Pointer); ok {
		name, ok := e.namedTypeName(ptr.Elem())
		if !ok {
			return nil, "", unsup("field selector on pointer to anonymous struct")
		}
		elemTy, err := e.emitType(ptr.Elem())
		if err != nil {
			return nil, "", err
		}
		return map[string]any{"expr": "deref", "ptr": base, "type": elemTy}, name, nil
	}
	name, ok := e.namedTypeName(recvType)
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
			index := seln.Index()
			// Method value on a TYPE-PARAMETER operand: re-resolve at the
			// substituted receiver, same rule as emitMethodCall (§4.3) —
			// without this the constraint interface would be mistaken for
			// the receiver and the UNBOXED operand fed to interface
			// dispatch.
			if e.curSubst != nil {
				opBase := types.Unalias(e.info.TypeOf(sel.X))
				if ptr, isPtr := opBase.(*types.Pointer); isPtr {
					opBase = types.Unalias(ptr.Elem())
				}
				if _, isTP := opBase.(*types.TypeParam); isTP {
					concrete := e.goTypeOf(sel.X)
					obj, idx, _ := types.LookupFieldOrMethod(concrete, true, e.pkg, sel.Sel.Name)
					m, isFunc := obj.(*types.Func)
					if !isFunc {
						return nil, unsup("method %s not found on substituted receiver %s",
							sel.Sel.Name, concrete)
					}
					fn, index = m, idx
				}
			}
			recvType := fn.Type().(*types.Signature).Recv().Type()
			if recvIface, isIface := recvType.Underlying().(*types.Interface); isIface {
				// Interface METHOD VALUE (design note D6): capture the BOX
				// now — fixed at value time (defer/defer-interface-value-eval)
				// — and dispatch through the anchor at the call. A NIL box
				// panics AT CREATION (the itab load; the hoisted check
				// below — interfaces/interface-method-value-nil pinned the
				// first cut's wrong panic-at-call assumption, audit F6).
				// Promotion through an embedded interface field walks to
				// the field value first.
				hops := index[:len(index)-1]
				var recvArg any
				var ifaceStatic types.Type
				var err error
				if len(hops) == 0 {
					ifaceStatic = e.goTypeOf(sel.X)
					recvArg, err = e.emitExpr(sel.X)
				} else {
					var base any
					base, err = e.emitExpr(sel.X)
					if err == nil {
						recvArg, ifaceStatic, err = e.fieldPathValue(base, e.goTypeOf(sel.X), hops)
					}
				}
				if err != nil {
					return nil, err
				}
				ifaceName, ok := e.ifaceWireName(ifaceStatic)
				if !ok {
					return nil, unsup("method value on unnameable interface type %s", ifaceStatic)
				}
				e.noteInterface(ifaceName, recvIface)
				e.noteCalledIfaceMethod(ifaceName+"."+fn.Name(), calledIfaceMethod{
					ifaceName: ifaceName, method: fn.Name(),
					sig:   fn.Type().(*types.Signature),
					subst: e.curSubst,
				})
				// Go panics AT CREATION if the interface is nil (the itab
				// load) — the first cut panicked at CALL time and the
				// oracle said created=0 (interface-method-value-nil). Hoist
				// the box once, nil-check it with the machine's runtime
				// panic payload, capture the temp.
				if e.hoistForbidden != "" {
					return nil, unsup("interface method value in %s", e.hoistForbidden)
				}
				gty, err := e.emitType(ifaceStatic)
				if err != nil {
					return nil, err
				}
				mvName := "$mv" + itoa(e.tmpSeq)
				e.tmpSeq++
				mvIdent := map[string]any{"expr": "ident", "name": mvName, "type": gty}
				e.hoisted = append(e.hoisted,
					map[string]any{"stmt": "assign", "define": true,
						"lhs": []any{map[string]any{"target": "declare", "id": mvName, "type": gty}},
						"rhs": []any{recvArg}},
					map[string]any{"stmt": "if",
						"cond": map[string]any{"expr": "binary", "op": "==",
							"x": mvIdent, "y": map[string]any{"expr": "nil"}, "operandType": gty},
						"then": map[string]any{"stmt": "panic", "runtimeError": true,
							"value": stringLitNode("runtime error: invalid memory address or nil pointer dereference")}})
				return map[string]any{"expr": "func-value",
					"func": ifaceName + "." + fn.Name(), "captured": []any{mvIdent}}, nil
			}
			defType := recvType
			pointerRecv := false
			if ptr, ok := recvType.(*types.Pointer); ok {
				defType = ptr.Elem()
				pointerRecv = true
			}
			name, ok := e.namedTypeName(defType)
			if !ok {
				return nil, unsup("method on anonymous type %s", defType)
			}
			// The receiver is captured AT METHOD-VALUE TIME, adjusted
			// through any embedded hops NOW (design note D1.2 — pinned by
			// embedding/promoted-method-value/{snapshot,live}).
			recvArg, err := e.promotedReceiverArg(sel, index[:len(index)-1], pointerRecv)
			if err != nil {
				return nil, err
			}
			return map[string]any{"expr": "func-value",
				"func": name + "." + fn.Name(), "captured": []any{recvArg}}, nil
		}
		if seln.Kind() == types.MethodExpr {
			// A METHOD EXPRESSION `T.M` / `I.M` (design note D6): the
			// receiver-first GoCore method function (declared method,
			// promotion wrapper, or interface dispatch anchor) IS the
			// method expression — a func value with no captures.
			fn, ok := seln.Obj().(*types.Func)
			if !ok {
				return nil, unsup("method expression %s is not a func", sel.Sel.Name)
			}
			sig := fn.Type().(*types.Signature)
			recvType := sig.Recv().Type()
			if recvIface, isIface := recvType.Underlying().(*types.Interface); isIface {
				ifaceStatic := e.goTypeOf(sel.X)
				ifaceName, ok := e.ifaceWireName(ifaceStatic)
				if !ok {
					return nil, unsup("method expression on unnameable interface type %s", ifaceStatic)
				}
				e.noteInterface(ifaceName, recvIface)
				e.noteCalledIfaceMethod(ifaceName+"."+fn.Name(), calledIfaceMethod{
					ifaceName: ifaceName, method: fn.Name(), sig: sig,
					subst: e.curSubst,
				})
				return map[string]any{"expr": "func-value",
					"func": ifaceName + "." + fn.Name(), "captured": []any{}}, nil
			}
			// Concrete receiver: the wire Func's receiver form must match
			// the expression's first parameter. Declared methods carry
			// their declaration receiver; a promoted entry's wrapper takes
			// T when the method is in T's own set, else *T. The one
			// mismatching shape — `(*T).M` over a method whose wire Func
			// takes T by value — needs a deref adapter; refuse precisely.
			// Unalias throughout (delta-review R3): under gotypesalias=1
			// a method expression named through an alias (`wrapAlias.Get`)
			// reaches here as a *types.Alias, and the raw Pointer/Named
			// assertions below mis-refused it (pinned by
			// methods/alias-promoted-method-expression).
			exprRecv := types.Unalias(e.goTypeOf(sel.X))
			baseT := exprRecv
			_, exprPtr := baseT.(*types.Pointer)
			if ptr, isPtr := baseT.(*types.Pointer); isPtr {
				baseT = types.Unalias(ptr.Elem())
			}
			name, ok := e.namedTypeName(baseT)
			if !ok {
				return nil, unsup("method expression on anonymous type %s", baseT)
			}
			wireRecvPtr := false
			if _, isPtr := recvType.(*types.Pointer); isPtr {
				wireRecvPtr = true
			}
			if len(seln.Index()) > 1 {
				named, isNamed := baseT.(*types.Named)
				if !isNamed {
					return nil, unsup("promoted method expression on non-named type %s", baseT)
				}
				wireRecvPtr = types.NewMethodSet(named).Lookup(fn.Pkg(), fn.Name()) == nil
			}
			if exprPtr && !wireRecvPtr {
				return nil, unsup("method expression (*%s).%s over a value-receiver method (deref adapter not modeled)", name, fn.Name())
			}
			return map[string]any{"expr": "func-value",
				"func": name + "." + fn.Name(), "captured": []any{}}, nil
		}
		return nil, unsup("non-field selector %s (method/expr)", sel.Sel.Name)
	}
	// PROMOTED field read (BUG-007, design note D1): flatten the embedded
	// hop path into field-get/deref chains.
	if index := e.promotedFieldIndex(sel); index != nil {
		base, err := e.emitExpr(sel.X)
		if err != nil {
			return nil, err
		}
		node, _, err := e.fieldPathValue(base, e.goTypeOf(sel.X), index)
		if err != nil {
			return nil, err
		}
		return node, nil
	}
	base, structName, err := e.fieldBase(sel)
	if err != nil {
		return nil, err
	}
	return map[string]any{"expr": "field-get", "recv": base, "typeId": structName, "field": sel.Sel.Name}, nil
}

func (e *emitter) emitIndex(ix *ast.IndexExpr) (any, error) {
	baseType := e.goTypeOf(ix.X).Underlying()
	base, err := e.emitExpr(ix.X)
	if err != nil {
		return nil, err
	}
	index, err := e.emitExpr(ix.Index)
	if err != nil {
		return nil, err
	}
	if m, ok := baseType.(*types.Map); ok {
		// Interface-typed key: box the lookup key so it compares against the
		// BOXED stored keys (raw-vs-boxed equality — maps/interface-key).
		index, err = e.wrapInterfaceConversion(m.Key(), e.goTypeOf(ix.Index), index)
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
		return map[string]any{"expr": "map-get", "base": base, "index": index, "keyType": keyTy, "valueType": valTy}, nil
	}
	return map[string]any{"expr": "index-get", "base": base, "index": index}, nil
}

func (e *emitter) emitStar(st *ast.StarExpr) (any, error) {
	ptr, err := e.emitExpr(st.X)
	if err != nil {
		return nil, err
	}
	pointee, err := e.emitType(e.goTypeOf(st))
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
		// &global is the statically resolved cell address itself (init
		// slice) — cell identity is the driver-seeded location, so
		// aliasing through the pointer observes the same cell as direct
		// reads (pinned by init/global-addr-taken).
		if v, ok := e.isPackageVar(e.info.Uses[ex]); ok {
			ga, ok := e.globalAddr(v)
			if !ok {
				return nil, unsup("package-level variable %s has no seeded cell", ex.Name)
			}
			return ga, nil
		}
		return map[string]any{"expr": "ref", "id": ex.Name}, nil
	case *ast.SelectorExpr:
		// PROMOTED field address (BUG-007, design note D1): the embedded
		// hop path flattens to a field-addr chain from the addressable
		// root (pointer hops read the pointer VALUE — heap identity).
		if index := e.promotedFieldIndex(ex); index != nil {
			node, _, err := e.fieldPathAddr(ex.X, index)
			return node, err
		}
		// Field ADDRESS: the machine's fieldAddr builds Loc.field on an
		// address operand (W4). A pointer base already IS the address (Go
		// auto-derefs p.n); an addressable value base recurses — so a.b.c
		// becomes fieldAddr(fieldAddr(ref a)). The old code passed the
		// base VALUE here, which is the root of the struct-field-write
		// backlog class (untriaged-count 2026-07-25 entry).
		bt := e.goTypeOf(ex.X)
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
		structName, ok := e.namedTypeName(defType)
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
		if _, isArray := e.goTypeOf(ex.X).Underlying().(*types.Array); isArray {
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
		return e.hoistNewFromValue(val, e.goTypeOf(ex))
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
		// Package-level variables assign through their cell address
		// (init slice), like every other addressed location.
		if v, ok := e.isPackageVar(e.info.Uses[id]); ok {
			ga, ok := e.globalAddr(v)
			if !ok {
				return nil, unsup("package-level variable %s has no seeded cell", id.Name)
			}
			return map[string]any{"target": "addr", "expr": ga}, nil
		}
		return map[string]any{"target": "var", "id": id.Name}, nil
	}
	// A map element is not addressable — outside the dedicated
	// single-assign fast path (mapAssign) it has no address to take, and
	// emitting index-addr would die as a runtime stuck instead of a
	// boundary refusal (audit 2026-07-26).
	if ix, ok := x.(*ast.IndexExpr); ok {
		if _, isMap := e.goTypeOf(ix.X).Underlying().(*types.Map); isMap {
			return nil, unsup("map element as assignment target outside a single assignment")
		}
	}
	addr, err := e.emitAddressOf(x)
	if err != nil {
		return nil, err
	}
	return map[string]any{"target": "addr", "expr": addr}, nil
}

func (e *emitter) emitCompositeLit(cl *ast.CompositeLit) (any, error) {
	t := e.goTypeOf(cl)
	switch u := t.Underlying().(type) {
	case *types.Struct:
		return e.emitStructLit(cl, t, u)
	case *types.Array:
		return e.emitArrayLit(cl, u)
	case *types.Slice:
		return e.emitSliceLit(cl, u)
	case *types.Map:
		return e.emitMapLit(cl, u)
	case *types.Pointer:
		// ELIDED &T (spec §Composite literals: "elements or keys that
		// are addresses of composite literals may elide the &T when the
		// element or key type is *T") — go/types gives the elided
		// literal the pointer type; lower it exactly like the explicit
		// &T{...} spelling (arc-final audit F12, 2026-08-06).
		if e.hoistForbidden != "" {
			return nil, unsup("&composite (elided) in %s", e.hoistForbidden)
		}
		elem := e.applySubst(u.Elem())
		var val any
		var err error
		switch eu := elem.Underlying().(type) {
		case *types.Struct:
			val, err = e.emitStructLit(cl, elem, eu)
		case *types.Array:
			val, err = e.emitArrayLit(cl, eu)
		case *types.Slice:
			val, err = e.emitSliceLit(cl, eu)
		case *types.Map:
			val, err = e.emitMapLit(cl, eu)
		default:
			return nil, unsup("composite literal of type %s", t)
		}
		if err != nil {
			return nil, err
		}
		return e.hoistNewFromValue(val, elem)
	default:
		return nil, unsup("composite literal of type %s", t)
	}
}

// hoistNewFromValue allocates an emitted composite value and returns the
// pointer temp (the shared lowering of explicit `&T{...}` and the elided
// composite-literal form).
func (e *emitter) hoistNewFromValue(val any, elem types.Type) (any, error) {
	elemTy, err := e.emitType(elem)
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
		ref, err := e.hoist(w, e.goTypeOf(kv.Value))
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
			w, err = e.wrapInterfaceConversion(fld.Type(), e.goTypeOf(positional[i]), w)
			if err != nil {
				return nil, err
			}
			args = append(args, w)
			continue
		}
		if ref, ok := preBound[fld.Name()]; ok {
			// The pre-bound temp holds the value at its static type; box the
			// temp reference into an interface-typed field.
			ref, err := e.wrapInterfaceConversion(fld.Type(), e.goTypeOf(keyed[fld.Name()]), ref)
			if err != nil {
				return nil, err
			}
			args = append(args, ref)
		} else if v, ok := keyed[fld.Name()]; ok {
			w, err := e.emitExpr(v)
			if err != nil {
				return nil, err
			}
			w, err = e.wrapInterfaceConversion(fld.Type(), e.goTypeOf(v), w)
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
		val := elt
		if kv, ok := elt.(*ast.KeyValueExpr); ok {
			tv, ok := e.info.Types[kv.Key]
			if !ok || tv.Value == nil {
				return nil, unsup("slice literal key is not constant")
			}
			idx, _ = constant.Int64Val(tv.Value)
			val = kv.Value
		}
		v, err := e.emitExpr(val)
		if err != nil {
			return nil, err
		}
		v, err = e.wrapInterfaceConversion(s.Elem(), e.goTypeOf(val), v)
		if err != nil {
			return nil, err
		}
		elems = append(elems, map[string]any{"index": idx, "value": v})
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
		k, err = e.wrapInterfaceConversion(m.Key(), e.goTypeOf(kv.Key), k)
		if err != nil {
			return nil, err
		}
		v, err := e.emitExpr(kv.Value)
		if err != nil {
			return nil, err
		}
		v, err = e.wrapInterfaceConversion(m.Elem(), e.goTypeOf(kv.Value), v)
		if err != nil {
			return nil, err
		}
		// An untyped-nil VALUE takes the map's element type: handled by
		// wrapInterfaceConversion above since the arc-final audit (F6 /
		// BUG-016 — the M1 site-local fix generalized to every
		// assignable context, same slice/map/pointer kind restriction;
		// BUG-014's defined-slice/-map elements stay the machine-side
		// gap, red-pinned by maps/nil-literal-values/defined-*-element).
		// First pinned by generics/type-aliases/nested-map (G4).
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
		val := elt
		if kv, ok := elt.(*ast.KeyValueExpr); ok {
			kv2, ok := e.info.Types[kv.Key]
			if !ok || kv2.Value == nil {
				return nil, unsup("array literal key is not constant")
			}
			k, _ := constant.Int64Val(kv2.Value)
			idx = k
			val = kv.Value
		}
		w, err := e.emitExpr(val)
		if err != nil {
			return nil, err
		}
		w, err = e.wrapInterfaceConversion(arr.Elem(), e.goTypeOf(val), w)
		if err != nil {
			return nil, err
		}
		elems = append(elems, map[string]any{"index": idx, "value": w})
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
		// A type-switch clause's implicit binding (`switch r := x.(type)`)
		// is declared INSIDE the literal but recorded in Implicits, not
		// Defs — without this it was mis-captured as an OUTER variable
		// (caught by panic-recover/recover-value's stage move).
		if cc, ok := n.(*ast.CaseClause); ok {
			if obj, ok2 := e.info.Implicits[cc]; ok2 {
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
		// Package-level variables are not captures: they resolve
		// statically to their driver-seeded cell (`globaladdr`, init
		// slice), so a literal's body reads and writes the shared cell
		// with no capture machinery (pinned by init/global-in-closure).
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
	sig, ok := e.goTypeOf(lit).(*types.Signature)
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
	savedFnRecv := e.fnHasRecv
	e.fnHasRecv = containsRecv(lit.Body)
	savedResults := e.curResults
	savedBranch, savedGoto := e.branchLabels, e.gotoLabels
	savedSeg, savedPC, savedLoop := e.gotoSeg, e.gotoPC, e.gotoLoop
	e.captureParam, e.hoisted = newCapture, nil
	e.curResults = sig.Results()
	e.branchLabels, e.gotoLabels = scanLabelUses(lit.Body)
	e.gotoSeg, e.gotoPC, e.gotoLoop = nil, "", ""
	var body any
	var berr error
	if len(e.gotoLabels) > 0 {
		body, berr = e.emitGotoBody(lit.Body)
	} else {
		body, berr = e.emitBlock(lit.Body)
	}
	e.captureParam, e.hoisted, e.curFuncName = savedCapture, savedHoisted, savedName
	e.fnHasRecv = savedFnRecv
	e.curResults = savedResults
	e.branchLabels, e.gotoLabels = savedBranch, savedGoto
	e.gotoSeg, e.gotoPC, e.gotoLoop = savedSeg, savedPC, savedLoop
	if berr != nil {
		return nil, berr
	}

	e.lifted = append(e.lifted, map[string]any{
		"name": name, "params": params, "results": results, "body": body,
		// A lifted literal's own signature keeps its variadic marker; the
		// prepended capture pointers are never variadic.
		"variadic": sig.Variadic(),
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
	if tv, ok := e.typesEntry(id); ok && tv.Value != nil {
		return e.emitConstValue(tv)
	}
	// A declared function used as a VALUE (`f := someFunc`) is a func value
	// with no captures — the same representation lifted literals get (§8).
	// Callee positions never reach here (emitCallNode handles them), so this
	// is exactly the value-position case. A GENERIC function in value
	// position is a value of the INSTANTIATED function (spec §Function
	// declarations — it cannot escape uninstantiated): go/types' Instances
	// carries the inference-completed arguments (assignment/return/call
	// targets — the higher-order-inference cluster), and the value names
	// the mangled stencil.
	if fn, ok := e.info.Uses[id].(*types.Func); ok {
		if sig, isSig := fn.Type().(*types.Signature); isSig {
			name := fn.Name()
			if sig.TypeParams().Len() > 0 {
				mangled, _, err := e.funcInstanceAt(id, fn)
				if err != nil {
					return nil, err
				}
				name = mangled
			}
			return map[string]any{"expr": "func-value", "func": name,
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
		// A package-level VARIABLE reads as a typed load from its
		// statically resolved, driver-seeded cell (init slice,
		// docs/2026-08-05_init-design.md §2). No frame-environment cell
		// exists for it, so a missing gid fails closed at the boundary.
		if v, ok := e.isPackageVar(obj); ok {
			ga, ok := e.globalAddr(v)
			if !ok {
				return nil, unsup("package-level variable %s has no seeded cell", id.Name)
			}
			ty, err := e.emitType(v.Type())
			if err != nil {
				return nil, err
			}
			return map[string]any{"expr": "deref", "ptr": ga, "type": ty}, nil
		}
	}
	return map[string]any{"expr": "ident", "name": id.Name}, nil
}

func (e *emitter) emitBasicLit(lit *ast.BasicLit) (any, error) {
	tv, _ := e.typesEntry(lit)
	return e.emitConstValue(tv)
}

func (e *emitter) emitConstValue(tv types.TypeAndValue) (any, error) {
	// A FLOAT-typed constant travels as its EXACT RATIONAL (floats design
	// note 2026-08-04, decision 5): num/den decimal strings from
	// go/constant's ExactString — every literal and every folded result is
	// exactly a rational — and GoCore performs the single spec-mandated
	// rounding at the typing boundary. Checked on the TYPE, not the value
	// kind: go/constant stores 3.0 with Int kind, which previously fell to
	// the int arm and emitted an untyped int literal into a float slot.
	if b, ok := tv.Type.Underlying().(*types.Basic); ok && b.Info()&types.IsFloat != 0 {
		switch tv.Value.Kind() {
		case constant.Int, constant.Float:
			num, den := exactRational(tv.Value)
			ty, err := e.emitBasic(b)
			if err != nil {
				return nil, err
			}
			return map[string]any{"expr": "float", "num": num, "den": den, "type": ty}, nil
		default:
			return nil, unsup("float-typed constant of kind %s", tv.Value.Kind())
		}
	}
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

// exactRational renders a go/constant Int or Float value as exact
// numerator/denominator decimal strings. ExactString of those kinds is
// either "n" or "n/d" with d > 0 (go/constant normalizes the sign into
// the numerator); the Lean decoder re-checks both fields and fails
// closed on any other shape.
func exactRational(v constant.Value) (string, string) {
	s := v.ExactString()
	if i := strings.IndexByte(s, '/'); i >= 0 {
		return s[:i], s[i+1:]
	}
	return s, "1"
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
	// (The binary-position left-operand pre-bind for receives was replaced
	// by the ONE-mechanism len/cap hoist under the function-scoped
	// `fnHasRecv` flag — BUG-023/BUG-026: every operand AND
	// statement-emission position, not just binary operands.)
	// The RHS of a short-circuit operator is only conditionally evaluated, so a
	// call there cannot be hoisted ahead of the operator.
	y, err := e.emitGuarded(op == "&&" || op == "||", "short-circuit operand", b.Y)
	if err != nil {
		return nil, err
	}
	// Mixed interface/non-interface comparison (spec §Comparison
	// operators: "A value x of non-interface type X and a value t of
	// interface type T can be compared if type X is comparable and X
	// implements T") — box the non-interface operand into the interface
	// type, exactly like every other interface-typed slot (BUG-017,
	// arc-final audit F4, 2026-08-06; the wrap itself no-ops on untyped
	// nil, so `i == nil` keeps its bare-nil lowering). The operand type
	// carried to GoCore is the INTERFACE side's.
	operandTypeExpr := b.X
	if op == "==" || op == "!=" {
		tx := e.applySubst(e.goTypeOf(b.X))
		ty := e.applySubst(e.goTypeOf(b.Y))
		xIsIface := tx != nil && types.IsInterface(tx)
		yIsIface := ty != nil && types.IsInterface(ty)
		if xIsIface && !yIsIface {
			if y, err = e.wrapInterfaceConversion(tx, e.goTypeOf(b.Y), y); err != nil {
				return nil, err
			}
		} else if yIsIface && !xIsIface {
			if x, err = e.wrapInterfaceConversion(ty, e.goTypeOf(b.X), x); err != nil {
				return nil, err
			}
			operandTypeExpr = b.Y
		}
	}
	node := map[string]any{"expr": "binary", "op": op, "x": x, "y": y}
	// Comparisons need the operand type in GoCore; carry it explicitly.
	if isComparison(op) {
		oty, err := e.typeOf(operandTypeExpr)
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

// emitUnaryExpr dispatches unary operators, routing & to address-of and
// <- (a receive in expression position) to the chan-recv hoist.
func (e *emitter) emitUnaryExpr(u *ast.UnaryExpr) (any, error) {
	if u.Op == token.AND {
		return e.emitAddressOf(u.X)
	}
	if u.Op == token.ARROW {
		return e.hoistChanRecv(u)
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
	return e.hoist(node, e.goTypeOf(c))
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
		tt := e.goTypeOf(c).Underlying()
		ot := e.goTypeOf(c.Args[0]).Underlying()
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
		// Conversion between BOOL-underlying types (`bool(x)` at a defined
		// bool, `T(b)` at a ~bool type set): bool has no representation
		// kinds, so the conversion is a pure static retyping — the runtime
		// value is unchanged and no machine convert op runs (the machine's
		// convert fails closed on bool targets). Static-type consequences
		// (interface boxing, dynamic type) come from go/types at the use
		// sites, never from this node.
		if tb, isTB := tt.(*types.Basic); isTB && tb.Kind() == types.Bool {
			if ob, isOB := ot.(*types.Basic); isOB && ob.Kind() == types.Bool {
				return arg, false, nil
			}
		}
		// An EXPLICIT conversion to an interface type is a box, exactly
		// like the implicit sites (`any(1)` in delete/index keys): emit
		// the to-interface wrap with the operand's static type as the
		// dynamic — the machine's convert op correctly refuses raw
		// values at interface targets (interfaces campaign, 2026-07-30).
		if converted, err := e.wrapInterfaceConversion(e.goTypeOf(c), e.goTypeOf(c.Args[0]), arg); err != nil {
			return nil, false, err
		} else if types.IsInterface(e.goTypeOf(c)) {
			return converted, false, nil
		}
		target, err := e.emitType(e.goTypeOf(c))
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
		lsig, _ := e.goTypeOf(lit).Underlying().(*types.Signature)
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

	// Generic function in callee position (mono.go): `f(x)` with inferred
	// arguments, or explicit `f[int](x)` / `f[a, b](x)` (parsed as
	// Index/IndexList). go/types' Instances carries the FULL inferred
	// argument list; the stencil is registered and the call targets the
	// mangled FuncId with the instantiated (concrete) signature.
	if id := e.genericCalleeIdent(c.Fun); id != nil {
		mangled, csig, err := e.funcInstanceAt(id, e.genericFuncObj(id))
		if err != nil {
			return nil, false, err
		}
		args, err := e.emitCallArgs(csig, c)
		if err != nil {
			return nil, false, err
		}
		resultTypes, err := e.emitResultTypes(csig)
		if err != nil {
			return nil, false, err
		}
		return map[string]any{"expr": "call", "func": mangled, "args": args,
			"resultTypes": resultTypes}, true, nil
	}

	fnID, ok := c.Fun.(*ast.Ident)
	if !ok {
		// Any other func-typed EXPRESSION in callee position (an indexed
		// func value `fns[i]()`, a parenthesized value, a field read) is a
		// call through the value — the §8 machinery.
		if vsig, ok := e.goTypeOf(c.Fun).Underlying().(*types.Signature); ok {
			callee, err := e.emitExpr(c.Fun)
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
		}
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

// genericFuncValue emits the func value of an explicitly instantiated
// generic function (`f[int]` in value position). handled=false means the
// base is not a generic-function identifier and the caller keeps its own
// refusal.
func (e *emitter) genericFuncValue(base ast.Expr) (any, error, bool) {
	id, ok := ast.Unparen(base).(*ast.Ident)
	if !ok {
		return nil, nil, false
	}
	fn := e.genericFuncObj(id)
	if fn == nil {
		return nil, nil, false
	}
	mangled, _, err := e.funcInstanceAt(id, fn)
	if err != nil {
		return nil, err, true
	}
	return map[string]any{"expr": "func-value", "func": mangled,
		"captured": []any{}}, nil, true
}

// genericCalleeIdent unwraps a callee expression to the identifier of a
// GENERIC function, when that is what it denotes: a bare ident (inferred
// instantiation) or an Index/IndexList whose base is one (explicit
// instantiation). Anything else — including index expressions over
// func-typed VALUES — returns nil and takes the ordinary paths.
func (e *emitter) genericCalleeIdent(fun ast.Expr) *ast.Ident {
	switch f := ast.Unparen(fun).(type) {
	case *ast.Ident:
		if e.genericFuncObj(f) != nil {
			return f
		}
	case *ast.IndexExpr:
		if id, ok := ast.Unparen(f.X).(*ast.Ident); ok && e.genericFuncObj(id) != nil {
			return id
		}
	case *ast.IndexListExpr:
		if id, ok := ast.Unparen(f.X).(*ast.Ident); ok && e.genericFuncObj(id) != nil {
			return id
		}
	}
	return nil
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
			if _, isTup := e.goTypeOf(inner).(*types.Tuple); isTup {
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
		// Interface-typed params: box non-interface arguments (a spread
		// argument's SLICE is exact — no interface wrap — but an untyped
		// NIL spread, `f(nil...)`, takes the variadic slice type itself:
		// the same one-mechanism nil typing as every other slot, BUG-016 /
		// arc-final audit F6).
		if sig != nil {
			params := sig.Params()
			args := []any{}
			for i, a := range c.Args {
				w, err := e.emitExpr(a)
				if err != nil {
					return nil, err
				}
				pi := i
				if pi >= params.Len() {
					pi = params.Len() - 1
				}
				if pi >= 0 {
					w, err = e.wrapInterfaceConversion(
						params.At(pi).Type(), e.goTypeOf(a), w)
					if err != nil {
						return nil, err
					}
				}
				args = append(args, w)
			}
			return args, nil
		}
		return e.emitArgs(c.Args)
	}
	fixed := sig.Params().Len() - 1
	args := []any{}
	for i := 0; i < fixed; i++ {
		w, err := e.emitExpr(c.Args[i])
		if err != nil {
			return nil, err
		}
		w, err = e.wrapInterfaceConversion(
			sig.Params().At(i).Type(), e.goTypeOf(c.Args[i]), w)
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
		w, err := e.emitExpr(c.Args[i])
		if err != nil {
			return nil, err
		}
		w, err = e.wrapInterfaceConversion(elemType, e.goTypeOf(c.Args[i]), w)
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
		// A call through a FUNC-TYPED FIELD (possibly promoted): an
		// ordinary call through the field's value (design note D6 —
		// functions/composite-function-values).
		if ok && seln.Kind() == types.FieldVal {
			if vsig, isSig := e.goTypeOf(sel).Underlying().(*types.Signature); isSig {
				callee, err := e.emitSelector(sel)
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
			}
		}
		return nil, false, unsup("selector call %s is not a method value", sel.Sel.Name)
	}
	fn, ok := seln.Obj().(*types.Func)
	if !ok {
		return nil, false, unsup("method %s is not a func", sel.Sel.Name)
	}
	index := seln.Index()
	// Constraint method call on a TYPE-PARAMETER operand (`x.Double()`
	// with x : T, mono.go / design note §4.3): the selection recorded by
	// go/types resolves against the CONSTRAINT, but the runtime value at
	// any instantiation is the plain concrete value — never an interface
	// box — so the selection re-resolves at the substituted receiver via
	// LookupFieldOrMethod and then takes the ordinary paths below (the
	// interface path only when the type ARGUMENT itself is an interface).
	if e.curSubst != nil {
		opBase := types.Unalias(e.info.TypeOf(sel.X))
		if ptr, isPtr := opBase.(*types.Pointer); isPtr {
			opBase = types.Unalias(ptr.Elem())
		}
		if _, isTP := opBase.(*types.TypeParam); isTP {
			concrete := e.goTypeOf(sel.X)
			obj, idx, _ := types.LookupFieldOrMethod(concrete, true, e.pkg, sel.Sel.Name)
			m, isFunc := obj.(*types.Func)
			if !isFunc {
				return nil, false, unsup("method %s not found on substituted receiver %s",
					sel.Sel.Name, concrete)
			}
			fn, index = m, idx
		}
	}
	recvType := fn.Type().(*types.Signature).Recv().Type()
	// Interface-receiver call: dynamic dispatch through the method-table
	// entry "<InterfaceName>.<Method>", the interface value itself as the
	// first argument — AS IS, no address-of or copy adjustment (the boxed
	// value carries its own receiver; methodReceiverArg's pointer logic is
	// for concrete receivers only).
	if recvIface, isIface := recvType.Underlying().(*types.Interface); isIface {
		// The interface VALUE being dispatched on: the receiver expression
		// itself, or — promotion through an embedded interface FIELD
		// (design note D1.4) — the field value reached by the hop walk (a
		// nil field then panics at dispatch, Go's nil-interface call).
		hops := index[:len(index)-1]
		var recvArg any
		var ifaceStatic types.Type
		if len(hops) == 0 {
			ifaceStatic = e.goTypeOf(sel.X)
			if _, ok := ifaceStatic.Underlying().(*types.Interface); !ok {
				return nil, false, unsup("interface method dispatch shape (non-interface receiver, no embedded hops)")
			}
			var err error
			recvArg, err = e.emitExpr(sel.X)
			if err != nil {
				return nil, false, err
			}
		} else {
			base, err := e.emitExpr(sel.X)
			if err != nil {
				return nil, false, err
			}
			node, ft, err := e.fieldPathValue(base, e.goTypeOf(sel.X), hops)
			if err != nil {
				return nil, false, err
			}
			recvArg, ifaceStatic = node, ft
		}
		ifaceName, ok := e.ifaceWireName(ifaceStatic)
		if !ok {
			return nil, false, unsup("method call on unnameable interface type %s", ifaceStatic)
		}
		// Record the dispatch target so emitProgram can synthesize a table
		// anchor when the interface is not declared in this package
		// (predeclared error, imported interfaces).
		e.noteInterface(ifaceName, recvIface)
		e.noteCalledIfaceMethod(ifaceName+"."+sel.Sel.Name, calledIfaceMethod{
			ifaceName: ifaceName, method: sel.Sel.Name,
			sig:   fn.Type().(*types.Signature),
			subst: e.curSubst,
		})
		args, err := e.emitCallArgs(fn.Type().(*types.Signature), c)
		if err != nil {
			return nil, false, err
		}
		all := append([]any{recvArg}, args...)
		resultTypes, err := e.emitResultTypes(fn.Type().(*types.Signature))
		if err != nil {
			return nil, false, err
		}
		return map[string]any{"expr": "call", "func": ifaceName + "." + sel.Sel.Name,
			"args": all, "resultTypes": resultTypes}, true, nil
	}
	// Defining type name (strip a pointer receiver) for the FuncId.
	defType := recvType
	pointerRecv := false
	if ptr, ok := recvType.(*types.Pointer); ok {
		defType = ptr.Elem()
		pointerRecv = true
	}
	name, ok := e.namedTypeName(defType)
	if !ok {
		return nil, false, unsup("method on anonymous type %s", defType)
	}
	// Receiver argument, adjusted through any embedded-field hops at the
	// call site (design note D1.2; see promotedReceiverArg for the rule).
	recvArg, err := e.promotedReceiverArg(sel, index[:len(index)-1], pointerRecv)
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
		node := any(map[string]any{"expr": tag, "operand": operand, "operandType": opTy})
		// A function containing a receive (BUG-023/BUG-026): len/cap are
		// spec-ordered calls but are emitted inline, while the receive
		// hoists to a statement — hoisting len/cap too keeps the lexical
		// left-to-right order (hoists append in emission order). Under
		// hoistForbidden the sweep cannot contain a receive (the receive
		// itself refuses there), so inline stays correct.
		//
		// The hoist is restricted to syntactically PANIC-FREE operands
		// (BUG-032): hoisting evaluates the operand ahead of the whole
		// statement, dragging its panic ahead of spec-unordered inline
		// panics to its left (`iv.(int) + len(b[j])` must realize gc's
		// left-to-right interface-conversion panic, dead receive or no).
		// A potentially-panicking operand in a receive-bearing function
		// FAILS CLOSED rather than picking between the two misorders
		// (inline loses the len-vs-receive order, hoisted loses the
		// operand-panic order) — pinned by
		// channels/recv-order/dead-recv-len-operand.
		if e.fnHasRecv && e.hoistForbidden == "" {
			if !e.panicFreeOperand(c.Args[0]) {
				return nil, false, unsup("%s of a potentially-panicking operand in a receive-bearing function (hoisting would reorder its panic — BUG-032)", name)
			}
			hoisted, err := e.hoist(node, e.goTypeOf(c))
			if err != nil {
				return nil, false, err
			}
			return hoisted, false, nil
		}
		return node, false, nil
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
		ptr, ok := e.goTypeOf(c).(*types.Pointer)
		if !ok {
			return nil, false, unsup("new result is not a pointer")
		}
		elemTy, err := e.emitType(ptr.Elem())
		if err != nil {
			return nil, false, err
		}
		// Go 1.26 accepts new(EXPR) too — allocate initialized with the
		// expression's value (the type form takes the zero value). The
		// original type-only arm silently default-initialized the value
		// form (new/new-expr/eval-once caught the expression never
		// evaluating).
		val := map[string]any{"expr": "default", "type": elemTy}
		if tv, ok := e.info.Types[c.Args[0]]; !ok || !tv.IsType() {
			w, err := e.emitExpr(c.Args[0])
			if err != nil {
				return nil, false, err
			}
			w, err = e.wrapInterfaceConversion(ptr.Elem(), e.goTypeOf(c.Args[0]), w)
			if err != nil {
				return nil, false, err
			}
			if m, ok := w.(map[string]any); ok {
				val = m
			} else {
				return nil, false, unsup("new operand emission shape")
			}
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
// bare nil ON THE WIRE — the MACHINE's panicPayload then maps a nil
// payload to the Go 1.21+ *runtime.PanicNilError runtime error, and the
// oracle runs with GODEBUG=panicnil=0 to match (arc-final audit F21,
// 2026-08-06, superseding §A2's legacy record — this docstring was
// corrected once before in the OTHER direction, unwinding-arc §A3
// finding 4; the semantics decision lives in panicPayload, not here).
func (e *emitter) emitPanicStmt(c *ast.CallExpr) (any, error) {
	if len(c.Args) != 1 {
		return nil, unsup("panic with %d arguments", len(c.Args))
	}
	arg := c.Args[0]
	t := e.goTypeOf(arg)
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
	// Defined non-struct types are identity-bearing since kind "defined"
	// landed (interfaces campaign; the BUG-004 refusal is lifted): their
	// wrap carries the defined type, so the boxed payload keeps its
	// identity and Go's qualified abort rendering.
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
	mt, ok := e.goTypeOf(c.Args[0]).Underlying().(*types.Map)
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
	// Interface-typed key: box, same as map reads/stores (the deleted key
	// compares against boxed stored keys — maps/delete-interface-dynamic-key).
	index, err = e.wrapInterfaceConversion(mt.Key(), e.goTypeOf(c.Args[1]), index)
	if err != nil {
		return nil, err
	}
	keyTy, err := e.emitType(mt.Key())
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "map-delete", "base": base, "index": index, "keyType": keyTy}, nil
}

// emitSortStmt lowers `slices.Sort(s)` at an INTEGER element kind onto the
// machine's sortSlice op (exact for integers — equal elements are
// indistinguishable, so Go's sort instability is unobservable). Everything
// else fails closed (docs/2026-07-30_quorum-extern-policy.md).
func (e *emitter) emitSortStmt(c *ast.CallExpr) (any, error) {
	if len(c.Args) != 1 {
		return nil, unsup("slices.Sort with %d arguments", len(c.Args))
	}
	sl, ok := e.goTypeOf(c.Args[0]).Underlying().(*types.Slice)
	if !ok {
		return nil, unsup("slices.Sort on non-slice %s", e.goTypeOf(c.Args[0]))
	}
	b, ok := sl.Elem().Underlying().(*types.Basic)
	if !ok || b.Info()&types.IsInteger == 0 {
		return nil, unsup("slices.Sort at non-integer element type %s", sl.Elem())
	}
	base, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, err
	}
	elemTy, err := e.emitType(sl.Elem())
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "sort-slice", "base": base, "elem": elemTy}, nil
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
	switch u := e.goTypeOf(c.Args[0]).Underlying().(type) {
	case *types.Map:
		return map[string]any{"stmt": "clear-map", "base": base}, nil
	case *types.Slice:
		elemTy, err := e.emitType(u.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"stmt": "clear-slice", "base": base, "elem": elemTy}, nil
	default:
		return nil, unsup("clear on %s", e.goTypeOf(c.Args[0]))
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
			"variadic": false,
			"body":     map[string]any{"stmt": "block", "body": []any{}},
		})
	}
	return map[string]any{"stmt": "defer",
		"callee": map[string]any{"expr": "func-value", "func": deferNoopName,
			"captured": []any{}},
		"args": []any{}}
}

// emitDeferClose lowers `defer close(ch)` (audit S6): a synthetic
// per-site closer function taking the channel as its one parameter, so
// the operand evaluates at defer time and the close runs at frame exit
// through the ordinary defer machinery.
func (e *emitter) emitDeferClose(c *ast.CallExpr) (any, error) {
	chGo := e.applySubst(e.goTypeOf(c.Args[0]))
	if _, ok := chGo.Underlying().(*types.Chan); !ok {
		return nil, unsup("defer close of non-channel %s", chGo)
	}
	chTy, err := e.emitType(chGo)
	if err != nil {
		return nil, err
	}
	chW, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, err
	}
	// Qualified by the enclosing function like every lifted literal
	// (BUG-027: liftSeq resets per function, so the bare name collided
	// across two functions and killed the whole package).
	name := e.curFuncName + "$deferClose" + itoa(e.liftSeq)
	e.liftSeq++
	e.lifted = append(e.lifted, map[string]any{
		"name": name,
		"params": []any{map[string]any{"id": "$ch", "type": chTy}},
		"results":  []any{},
		"variadic": false,
		"body": map[string]any{"stmt": "block", "body": []any{
			map[string]any{"stmt": "chan-close",
				"ch": map[string]any{"expr": "ident", "name": "$ch", "type": chTy}},
		}},
	})
	return map[string]any{"stmt": "defer",
		"callee": map[string]any{"expr": "func-value", "func": name,
			"captured": []any{}},
		"args": []any{chW}}, nil
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
	if isStringType(e.goTypeOf(x).Underlying()) {
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
	resTy := e.goTypeOf(c)
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
			w, err := e.emitExpr(c.Args[i])
			if err != nil {
				return nil, false, err
			}
			w, err = e.wrapInterfaceConversion(sl.Elem(), e.goTypeOf(c.Args[i]), w)
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
	t := e.goTypeOf(c.Args[0])
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
	case *types.Chan:
		// make(chan T[, n]) (channels arc slice 1). A negative runtime n
		// is the machine's recoverable "makechan: size out of range"
		// panic; the type argument may itself be directional
		// (make(<-chan int, 2) is legal — a channel nothing can send on).
		elemTy, err := e.emitType(u.Elem())
		if err != nil {
			return nil, false, err
		}
		node := map[string]any{"stmt": "make-chan", "target": target, "elem": elemTy}
		if len(c.Args) >= 2 {
			capArg, err := e.emitExpr(c.Args[1])
			if err != nil {
				return nil, false, err
			}
			node["cap"] = capArg
		}
		e.hoisted = append(e.hoisted, node)
		return ref, false, nil
	default:
		return nil, false, unsup("make of %s", t)
	}
}

// ---- channels (channels arc slice 1) ----

// containsRecv reports whether a node syntactically contains a channel
// receive, WITHOUT descending into func literals (their bodies evaluate
// at call time and scan their own bodies at emitFuncLit). Spec §Order of
// evaluation: function calls AND receive operations are ordered
// lexically left-to-right — a receive hoists to a statement (it can
// block), so any spec-ordered evaluation LEFT of it that is not itself
// hoisted (len/cap) must hoist too, which is what the function-scoped
// `fnHasRecv` flag drives (BUG-023/BUG-026).
func containsRecv(x ast.Node) bool {
	found := false
	ast.Inspect(x, func(n ast.Node) bool {
		if found {
			return false
		}
		switch n := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.UnaryExpr:
			if n.Op == token.ARROW {
				found = true
				return false
			}
		}
		return true
	})
	return found
}

// panicFreeOperand reports whether evaluating x can NEVER panic —
// conservatively syntactic: identifiers, basic literals, parens, and
// selector chains free of pointer indirection (an implicit nil deref
// can panic). Used to keep the fnHasRecv len/cap hoist
// order-transparent (BUG-032): only a panic-free operand may move ahead
// of the statement without reordering a spec-unordered panic.
func (e *emitter) panicFreeOperand(x ast.Expr) bool {
	switch v := ast.Unparen(x).(type) {
	case *ast.Ident:
		return true
	case *ast.BasicLit:
		return true
	case *ast.SelectorExpr:
		// Round 4 (BUG-039): a selection can dereference IMPLICITLY —
		// promotion through an embedded POINTER field nil-derefs with no
		// pointer visible in the syntax. go/types knows: any selection
		// that indirects is not panic-free.
		if sel, ok := e.info.Selections[v]; ok && sel.Indirect() {
			return false
		}
		t := e.goTypeOf(v.X)
		if t == nil {
			// Package qualifier: the selector reads a package-level
			// variable — no indirection, no panic.
			return true
		}
		if _, isPtr := e.applySubst(t).Underlying().(*types.Pointer); isPtr {
			return false
		}
		return e.panicFreeOperand(v.X)
	}
	return false
}

// chanElem resolves an expression's channel element type (substitution-
// aware for stencils).
func (e *emitter) chanElem(chExpr ast.Expr) (types.Type, error) {
	if ch, ok := e.applySubst(e.goTypeOf(chExpr)).Underlying().(*types.Chan); ok {
		return ch.Elem(), nil
	}
	return nil, unsup("receive from non-channel %s", e.goTypeOf(chExpr))
}

// emitCloseStmt lowers the builtin close(ch) statement.
func (e *emitter) emitCloseStmt(c *ast.CallExpr) (any, error) {
	if len(c.Args) != 1 {
		return nil, unsup("close with %d arguments", len(c.Args))
	}
	chW, err := e.emitExpr(c.Args[0])
	if err != nil {
		return nil, err
	}
	return map[string]any{"stmt": "chan-close", "ch": chW}, nil
}

// hoistChanRecv lowers a receive in EXPRESSION position: a receive is a
// STATEMENT in GoCore (it may block or panic), so it hoists into a fresh
// temp bound by a chan-recv statement; the A-normal-form hoist discipline
// preserves Go's left-to-right evaluation order (pinned by
// channels/make-edge/ordinary-receive-eval-order).
func (e *emitter) hoistChanRecv(u *ast.UnaryExpr) (any, error) {
	if e.hoistForbidden != "" {
		return nil, unsup("channel receive in %s (would change evaluation order)", e.hoistForbidden)
	}
	elemGo, err := e.chanElem(u.X)
	if err != nil {
		return nil, err
	}
	elemTy, err := e.emitType(elemGo)
	if err != nil {
		return nil, err
	}
	chW, err := e.emitExpr(u.X)
	if err != nil {
		return nil, err
	}
	name := "$c" + itoa(e.tmpSeq)
	e.tmpSeq++
	e.hoisted = append(e.hoisted, map[string]any{
		"stmt":    "chan-recv",
		"targets": []any{map[string]any{"target": "declare", "id": name, "type": elemTy}},
		"ch":      chW,
		"elem":    elemTy,
	})
	return map[string]any{"expr": "ident", "name": name, "type": elemTy}, nil
}

// emitMapTargetWire builds the machine's MAP-element delivery target
// (convergence round, BUG-030): base and key evaluate in the machine's
// phase 1 (post-communication, in lexical position among the targets —
// the BUG-028 point), and the map store is a phase-2 left-to-right
// step, so it lands before a LATER target's store panic. The map VALUE
// must not need interface boxing (the machine stores the delivered
// value raw) — callers check.
func (e *emitter) emitMapTargetWire(ix *ast.IndexExpr, m *types.Map) (any, error) {
	baseW, err := e.emitExpr(ix.X)
	if err != nil {
		return nil, err
	}
	idxW, err := e.emitExpr(ix.Index)
	if err != nil {
		return nil, err
	}
	idxW, err = e.wrapInterfaceConversion(m.Key(), e.goTypeOf(ix.Index), idxW)
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
	return map[string]any{"target": "map", "base": baseW, "index": idxW,
		"keyType": keyTy, "valueType": valTy}, nil
}

// emitChanRecvAssign lowers the receive STATEMENT forms `v = <-ch`,
// `v, ok := <-ch`, … to the dedicated chan-recv statement (spec
// §Assignments' two phases: the machine performs the COMMUNICATION
// first, evaluates target operands, and stores left-to-right after —
// BUG-022/BUG-029). A blank ok drops to the 1-target form (the flag is
// unobservable); a blank value receives into a fresh temp (the receive
// itself must still happen). A MAP-element target in the TWO-target
// form rides the machine's delivery plan as a "map" target (BUG-030:
// its store must land before the second target's store); the
// single-target form `m[k] = <-ch` keeps the post-statement map-assign
// (only one store, so order cannot be violated, and it supports
// interface-valued maps via the boxing wrap the machine target cannot
// carry).
func (e *emitter) emitChanRecvAssign(st *ast.AssignStmt, ux *ast.UnaryExpr, define bool) (any, error) {
	elemGo, err := e.chanElem(ux.X)
	if err != nil {
		return nil, err
	}
	elemTy, err := e.emitType(elemGo)
	if err != nil {
		return nil, err
	}
	boolTy := map[string]any{"kind": "bool"}
	targets := []any{}
	post := []any{}
	// One target position: pos 0 receives the element (type elemGo/elemTy),
	// pos 1 the ok flag (bool).
	emitPos := func(lv ast.Expr, posGo types.Type, posTy any) error {
		if id, ok := lv.(*ast.Ident); ok && id.Name == "_" {
			if len(st.Lhs) == 2 && lv == st.Lhs[1] {
				// blank ok: drop to the 1-target form (unobservable)
				return nil
			}
			name := "$c" + itoa(e.tmpSeq)
			e.tmpSeq++
			targets = append(targets, map[string]any{"target": "declare", "id": name, "type": posTy})
			return nil
		}
		if ix, ok := ast.Unparen(lv).(*ast.IndexExpr); ok {
			if m, ok := e.applySubst(e.goTypeOf(ix.X)).Underlying().(*types.Map); ok {
				if len(st.Lhs) == 2 {
					// TWO-target form (BUG-030): the map store is a phase-2
					// left-to-right store and must land BEFORE the other
					// target's store — carry the target into the machine's
					// delivery plan. The machine stores the delivered value
					// raw, so an interface-valued map with a concrete
					// element needs boxing it cannot do: fail closed.
					if types.IsInterface(m.Elem()) && !types.IsInterface(posGo) {
						return unsup("channel receive into interface-valued map element (two-target form)")
					}
					w, err := e.emitMapTargetWire(ix, m)
					if err != nil {
						return err
					}
					targets = append(targets, w)
					return nil
				}
				// Single-target map element: the receive lands in a fresh
				// temp; the map-assign stores it AFTER the communication.
				// Base and key are emitted INLINE into that post-receive
				// store (BUG-028): calls in them auto-hoist pre-receive
				// (A-normal form) and len(ch) keys hoist via the
				// fnHasRecv flag — both spec-ordered, both pre-receive —
				// while a panicking NON-call operand (spec-unordered
				// against the receive) fires post-receive, matching gc's
				// receive-first realization like the sibling
				// pointer/slice target arm.
				baseW, err := e.emitExpr(ix.X)
				if err != nil {
					return err
				}
				idxW, err := e.emitExpr(ix.Index)
				if err != nil {
					return err
				}
				idxW, err = e.wrapInterfaceConversion(m.Key(), e.goTypeOf(ix.Index), idxW)
				if err != nil {
					return err
				}
				name := "$c" + itoa(e.tmpSeq)
				e.tmpSeq++
				targets = append(targets, map[string]any{"target": "declare", "id": name, "type": posTy})
				valW, err := e.wrapInterfaceConversion(m.Elem(), posGo,
					any(map[string]any{"expr": "ident", "name": name, "type": posTy}))
				if err != nil {
					return err
				}
				keyTy, err := e.emitType(m.Key())
				if err != nil {
					return err
				}
				valTy, err := e.emitType(m.Elem())
				if err != nil {
					return err
				}
				post = append(post, map[string]any{"stmt": "map-assign", "base": baseW,
					"index": idxW, "value": valW, "keyType": keyTy, "valueType": valTy})
				return nil
			}
		}
		// The statement form stores the RAW value; an interface-typed
		// target would need the boxing wrap the statement does not carry —
		// fail closed (the := forms always type the target at the element
		// type; map-element targets above box through map-assign).
		tgtTy := e.applySubst(e.assignTargetType(lv, define))
		if tgtTy != nil && types.IsInterface(tgtTy) && !types.IsInterface(posGo) {
			return unsup("channel receive into interface-typed target")
		}
		w, err := e.emitAssignTarget(lv, define)
		if err != nil {
			return err
		}
		targets = append(targets, w)
		return nil
	}
	if err := emitPos(st.Lhs[0], elemGo, elemTy); err != nil {
		return nil, err
	}
	if len(st.Lhs) == 2 {
		if err := emitPos(st.Lhs[1], types.Typ[types.Bool], boolTy); err != nil {
			return nil, err
		}
	}
	chW, err := e.emitExpr(ux.X)
	if err != nil {
		return nil, err
	}
	node := any(map[string]any{"stmt": "chan-recv", "targets": targets, "ch": chW, "elem": elemTy})
	if len(post) > 0 {
		node = map[string]any{"stmt": "block", "body": append([]any{node}, post...)}
	}
	return node, nil
}

// machineSelectTargets tries to express EVERY user target of a select
// receive clause as a machine delivery target (convergence round,
// BUG-029 select half): the machine then realizes spec step 4 with the
// SAME two-phase split as the receive statement — phase-1 operand
// evaluation, phase-2 left-to-right stores — where body-side single
// assigns interleave a later target's address evaluation with an
// earlier store (the exact BUG-029 collapse; pinned by
// channels/select-recv-edge/*). Returns ok=false (fall back to the
// temp+body-assign lowering) when a target is blank, needs interface
// boxing (the machine stores the delivered value raw), or emits operand
// HOISTS — a hoisted temp would evaluate at select ENTRY, but step 4
// evaluates targets only after selection (pinned by
// unselected-receive-lhs-not-eval).
func (e *emitter) machineSelectTargets(lhs []ast.Expr, elemGo types.Type) ([]any, bool, error) {
	ws := []any{}
	for i, lv := range lhs {
		if id, ok := lv.(*ast.Ident); ok && id.Name == "_" {
			return nil, false, nil
		}
		posGo := elemGo
		if i == 1 {
			posGo = types.Typ[types.Bool]
		}
		var w any
		var hoists []any
		if ix, ok := ast.Unparen(lv).(*ast.IndexExpr); ok {
			if m, ok := e.applySubst(e.goTypeOf(ix.X)).Underlying().(*types.Map); ok {
				// Map-element target (BUG-030): machine "map" target unless
				// the VALUE needs boxing.
				if types.IsInterface(m.Elem()) && !types.IsInterface(posGo) {
					return nil, false, nil
				}
				saved := e.hoisted
				e.hoisted = nil
				mw, err := e.emitMapTargetWire(ix, m)
				hoists = e.hoisted
				e.hoisted = saved
				if err != nil {
					return nil, false, err
				}
				if len(hoists) > 0 {
					return nil, false, nil
				}
				ws = append(ws, mw)
				continue
			}
		}
		tgtTy := e.applySubst(e.assignTargetType(lv, false))
		if tgtTy != nil && types.IsInterface(tgtTy) && !types.IsInterface(posGo) {
			return nil, false, nil
		}
		saved := e.hoisted
		e.hoisted = nil
		w, err := e.emitAssignTarget(lv, false)
		hoists = e.hoisted
		e.hoisted = saved
		if err != nil {
			return nil, false, err
		}
		if len(hoists) > 0 {
			return nil, false, nil
		}
		ws = append(ws, w)
	}
	return ws, true, nil
}

// selectRecvClause builds one receive clause of a select. Plain lvalue
// user targets ride the clause head as MACHINE delivery targets
// (machineSelectTargets — spec step 4 with the statement form's
// two-phase split, BUG-029). Otherwise the received value (and ok flag)
// land in fresh pre-declared temps and the USER assignment happens at
// the top of the clause body (step 4's side effects stay inside the
// selected clause — pinned by
// channels/select-deterministic/{unselected-receive-lhs-not-eval,
// selected-receive-lhs-eval}).
func (e *emitter) selectRecvClause(ux *ast.UnaryExpr, lhs []ast.Expr, define bool, bodyNode any) (any, error) {
	elemGo, err := e.chanElem(ux.X)
	if err != nil {
		return nil, err
	}
	elemTy, err := e.emitType(elemGo)
	if err != nil {
		return nil, err
	}
	chW, err := e.emitExpr(ux.X)
	if err != nil {
		return nil, err
	}
	if !define && len(lhs) > 0 {
		ws, ok, err := e.machineSelectTargets(lhs, elemGo)
		if err != nil {
			return nil, err
		}
		if ok {
			return map[string]any{"clause": "recv", "targets": ws, "ch": chW,
				"elem": elemTy, "body": bodyNode}, nil
		}
	}
	// Temp-fallback lowering. Round 4 (BUG-036): the user write-back is
	// ONE body-side multi-assign — per-target single assigns interleaved
	// an earlier store with a later target's address operands, the exact
	// phase collapse the spine removed; a single "assign" statement rides
	// the machine's phase-split plan, and clause locality still holds
	// (temps, hoists and the write-back all sit inside the clause body,
	// hoists of BOTH targets before both stores).
	boolTy := map[string]any{"kind": "bool"}
	targets := []any{}
	prefix := []any{}
	userLhs := []any{}
	userRhs := []any{}
	if len(lhs) > 0 {
		vName := "$c" + itoa(e.tmpSeq)
		e.tmpSeq++
		targets = append(targets, map[string]any{"target": "declare", "id": vName, "type": elemTy})
		if id, ok := lhs[0].(*ast.Ident); !ok || id.Name != "_" {
			// The user assignment's own operand hoists (an effectful LHS
			// index, an interface boxing) must stay INSIDE the clause body.
			saved := e.hoisted
			e.hoisted = nil
			w, err := e.emitAssignTarget(lhs[0], define)
			if err != nil {
				e.hoisted = saved
				return nil, err
			}
			rhs := any(map[string]any{"expr": "ident", "name": vName, "type": elemTy})
			rhs, err = e.wrapInterfaceConversion(e.applySubst(e.assignTargetType(lhs[0], define)), elemGo, rhs)
			if err != nil {
				e.hoisted = saved
				return nil, err
			}
			prefix = append(prefix, e.hoisted...)
			e.hoisted = saved
			userLhs = append(userLhs, w)
			userRhs = append(userRhs, rhs)
		}
		if len(lhs) == 2 {
			okName := "$c" + itoa(e.tmpSeq)
			e.tmpSeq++
			targets = append(targets, map[string]any{"target": "declare", "id": okName, "type": boolTy})
			if id, ok := lhs[1].(*ast.Ident); !ok || id.Name != "_" {
				saved := e.hoisted
				e.hoisted = nil
				w, err := e.emitAssignTarget(lhs[1], define)
				if err != nil {
					e.hoisted = saved
					return nil, err
				}
				prefix = append(prefix, e.hoisted...)
				e.hoisted = saved
				userLhs = append(userLhs, w)
				userRhs = append(userRhs, map[string]any{"expr": "ident", "name": okName, "type": boolTy})
			}
		}
	}
	if len(userLhs) > 0 {
		prefix = append(prefix, map[string]any{"stmt": "assign", "define": define,
			"lhs": userLhs, "rhs": userRhs})
	}
	body := bodyNode
	if len(prefix) > 0 {
		body = map[string]any{"stmt": "block", "body": append(prefix, bodyNode)}
	}
	return map[string]any{"clause": "recv", "targets": targets, "ch": chW, "elem": elemTy, "body": body}, nil
}

// emitSelect lowers a select statement (channels arc slice 1): clause
// channel operands and send RHS values are emitted in source order — their
// effectful subexpressions ride the statement-level hoists, realizing the
// spec's entry-time once-in-source-order evaluation (step 1) — and the
// whole statement wraps in "breakable" (a select body's `break` exits the
// select, like switch). The machine commits exactly-one-ready or default;
// multi-ready fails closed there (slice 4).
func (e *emitter) emitSelect(st *ast.SelectStmt) (any, error) {
	clauses := []any{}
	var defaultBody any
	for _, s := range st.Body.List {
		cc, ok := s.(*ast.CommClause)
		if !ok {
			return nil, unsup("select clause %T", s)
		}
		body, err := e.emitStmtList(cc.Body)
		if err != nil {
			return nil, err
		}
		bodyNode := any(map[string]any{"stmt": "block", "body": body})
		if cc.Comm == nil {
			if defaultBody != nil {
				return nil, unsup("select with multiple default cases")
			}
			defaultBody = bodyNode
			continue
		}
		switch comm := cc.Comm.(type) {
		case *ast.SendStmt:
			ch, ok := e.applySubst(e.goTypeOf(comm.Chan)).Underlying().(*types.Chan)
			if !ok {
				return nil, unsup("select send on non-channel %s", e.goTypeOf(comm.Chan))
			}
			chW, err := e.emitExpr(comm.Chan)
			if err != nil {
				return nil, err
			}
			valW, err := e.emitExpr(comm.Value)
			if err != nil {
				return nil, err
			}
			valW, err = e.wrapInterfaceConversion(ch.Elem(), e.goTypeOf(comm.Value), valW)
			if err != nil {
				return nil, err
			}
			elemTy, err := e.emitType(ch.Elem())
			if err != nil {
				return nil, err
			}
			clauses = append(clauses, map[string]any{"clause": "send", "ch": chW, "value": valW, "elem": elemTy, "body": bodyNode})
		case *ast.ExprStmt:
			ux, isU := ast.Unparen(comm.X).(*ast.UnaryExpr)
			if !isU || ux.Op != token.ARROW {
				return nil, unsup("select receive clause shape %T", comm.X)
			}
			node, err := e.selectRecvClause(ux, nil, false, bodyNode)
			if err != nil {
				return nil, err
			}
			clauses = append(clauses, node)
		case *ast.AssignStmt:
			if len(comm.Rhs) != 1 {
				return nil, unsup("select receive clause arity")
			}
			ux, isU := ast.Unparen(comm.Rhs[0]).(*ast.UnaryExpr)
			if !isU || ux.Op != token.ARROW {
				return nil, unsup("select receive clause shape %T", comm.Rhs[0])
			}
			if len(comm.Lhs) < 1 || len(comm.Lhs) > 2 {
				return nil, unsup("select receive with %d targets", len(comm.Lhs))
			}
			node, err := e.selectRecvClause(ux, comm.Lhs, comm.Tok == token.DEFINE, bodyNode)
			if err != nil {
				return nil, err
			}
			clauses = append(clauses, node)
		default:
			return nil, unsup("select communication %T", cc.Comm)
		}
	}
	node := map[string]any{"stmt": "select", "clauses": clauses}
	if defaultBody != nil {
		node["default"] = defaultBody
	}
	return map[string]any{"stmt": "breakable", "body": node}, nil
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
