package main

// hiddendep.go — the E7 fail-closed hidden-dependency-shape detector
// (t1-fidelity-fixes, 2026-08-31; the charter-era E7 ruling ordered
// this interim guard to ship FIRST — docs/2026-08-11_latitude-inventory.md
// §E7 — and it never had until now).
//
// THE HOLE IT CLOSES. spec#Package_initialization: "If other, hidden,
// data dependencies exists between variables, the initialization order
// between those variables is unspecified." The frontend realizes
// go/types' InitOrder; gc's initorder is a separate, coarser analysis,
// and the two are PROBED to diverge on exactly the spec's own example
// shape (the init/hidden-dep-order deviation pin: go/types runs the
// hidden-dep initializer FIRST, gc runs it after its hidden
// prerequisites — both conforming). Until this detector, any NEW
// hidden-dep program lowered without complaint and silently realized
// an order that does not transfer to gc — the census's worst live
// combination (soundness-direction, silent, cheap to guard;
// assessment A1-15).
//
// THE PREDICATE (fires only when the divergence is OBSERVABLE, not on
// mere presence of an interface call — the design constraint on this
// guard):
//
//  1. REACH: a kept (non-quarantined) package-level initializer's
//     expression, or a function/method/func-literal body it reaches
//     through STATICALLY-RESOLVED calls, contains a method call
//     dispatched THROUGH AN INTERFACE (go/types Selections: MethodVal
//     with an interface receiver). Interface dispatch is precisely
//     what the reference-based dependency analyses cannot see through
//     — the hidden-dep channel of the spec's own example.
//  2. OBSERVABLE: some method with the dispatched NAME, declared in
//     the SAME UNIT as the initializer, references a package-level
//     variable of that unit that itself has a kept initializer. Only
//     then can the hidden edge reorder an observable initialization
//     (methods of OTHER units read their own unit's variables, and
//     dependency units are fully initialized before this unit's
//     variables start — the program schedule fixes cross-unit order).
//
// Both conditions are conservative over-approximations in the sound
// direction: a static reach that never executes, or a name-matched
// method the dynamic dispatch can never select, produces a REFUSAL of
// a program the machine could have run — visible, never wrong.
//
// RECORDED RESIDUAL (deliberate scope boundary, not an oversight):
// dispatch through FUNCTION VALUES (`var f func(); f()` in an
// initializer, method values escaping into init) is a distinct,
// rarer hidden channel this detector does not cover — covering it
// syntactically would flag every closure call inside the injected
// stdlib shims. E7's probed divergence and the spec's example are the
// interface shape; the func-value channel stays on E7's re-envelope
// obligation.
//
// THE ALLOW. The recorded deviation case (init/hidden-dep-order) is
// the one program that must keep lowering: its differential red IS the
// version-tracked deviation record, and scripts/check-frontend-pins
// pins the realized order end-to-end. The allow is EXPLICIT and lives
// in the APPARATUS, not in user source: the frontend flag
// --allow-hidden-dep-init-order, passed only for that case id by
// scripts/diff-coverage and by scripts/check-frontend-pins. Under the
// flag the detector still runs and prints its finding to stderr as a
// WARNING — visible every time — and the export proceeds.

import (
	"fmt"
	"go/ast"
	"go/types"
	"os"
)

// allowHiddenDepInitOrder is set by --allow-hidden-dep-init-order
// (main.go): downgrade the E7 refusal to a stderr warning. Reserved to
// the apparatus for the recorded deviation pin; see the file comment.
var allowHiddenDepInitOrder bool

// checkHiddenDepInitOrder runs the detector over every unit's kept
// initializers. Called from emitProgram after the H-11 quarantine
// pre-pass (quarantined initializers do not run, so they are neither
// roots nor observable targets). Returns the E7 refusal, or nil.
func (e *emitter) checkHiddenDepInitOrder() error {
	// Program-wide callee index: function/method object -> its body
	// and owning unit (bodies must be walked under their own unit's
	// types.Info).
	type declBody struct {
		body *ast.BlockStmt
		unit *sourcePkg
	}
	bodies := map[types.Object]declBody{}
	for _, u := range e.units {
		for _, f := range u.files {
			for _, d := range f.Decls {
				fd, ok := d.(*ast.FuncDecl)
				if !ok || fd.Body == nil {
					continue
				}
				if obj := u.info.Defs[fd.Name]; obj != nil {
					bodies[obj] = declBody{fd.Body, u}
				}
			}
		}
	}

	for _, u := range e.units {
		// Kept initialized package-level variables of this unit — the
		// observable targets, and the owners of the root expressions.
		initVars := map[types.Object]bool{}
		for _, ini := range u.info.InitOrder {
			if e.quarantinedInits[ini.Rhs] {
				continue
			}
			for _, v := range ini.Lhs {
				if v.Name() != "_" {
					initVars[v] = true
				}
			}
		}
		if len(initVars) == 0 {
			continue
		}

		// Same-unit methods by name, for the observability gate.
		methodsByName := map[string][]declBody{}
		for _, f := range u.files {
			for _, d := range f.Decls {
				if fd, ok := d.(*ast.FuncDecl); ok && fd.Recv != nil && fd.Body != nil {
					methodsByName[fd.Name.Name] = append(methodsByName[fd.Name.Name], declBody{fd.Body, u})
				}
			}
		}

		// methodReadsInitVar: the observability gate for a dispatched
		// name — some same-unit method of that name references a kept
		// initialized package variable of this unit.
		methodReadsInitVar := func(name string) (string, bool) {
			for _, mb := range methodsByName[name] {
				var hit string
				ast.Inspect(mb.body, func(n ast.Node) bool {
					if hit != "" {
						return false
					}
					if id, ok := n.(*ast.Ident); ok {
						if obj := mb.unit.info.Uses[id]; obj != nil && initVars[obj] {
							hit = obj.Name()
							return false
						}
					}
					return true
				})
				if hit != "" {
					return hit, true
				}
			}
			return "", false
		}

		for _, ini := range u.info.InitOrder {
			if e.quarantinedInits[ini.Rhs] {
				continue
			}
			// Reachability worklist from the initializer expression:
			// each entry is a node walked under its unit's info.
			type workItem struct {
				node ast.Node
				unit *sourcePkg
			}
			work := []workItem{{ini.Rhs, u}}
			seen := map[types.Object]bool{}
			var e7 error
			for len(work) > 0 && e7 == nil {
				it := work[0]
				work = work[1:]
				ast.Inspect(it.node, func(n ast.Node) bool {
					if e7 != nil {
						return false
					}
					call, ok := n.(*ast.CallExpr)
					if !ok {
						return true
					}
					// Resolve the callee statically; queue bodies.
					switch fun := ast.Unparen(call.Fun).(type) {
					case *ast.Ident:
						if obj := it.unit.info.Uses[fun]; obj != nil {
							if fn, isFn := obj.(*types.Func); isFn && !seen[fn] {
								seen[fn] = true
								if db, ok := bodies[fn]; ok {
									work = append(work, workItem{db.body, db.unit})
								}
							}
						}
					case *ast.SelectorExpr:
						if sel, ok := it.unit.info.Selections[fun]; ok && sel.Kind() == types.MethodVal {
							if types.IsInterface(sel.Recv()) {
								// The hidden-dep channel. Fire only if
								// observable: a method of this name in
								// the INITIALIZER's unit reads a kept
								// initialized var of that unit. (The
								// interface call may sit in a reached
								// body of ANOTHER unit, but the
								// initializer unit's types flow
								// anywhere, so the gate is always the
								// initializer unit's.)
								if varName, obs := methodReadsInitVar(fun.Sel.Name); obs {
									names := make([]string, 0, len(ini.Lhs))
									for _, v := range ini.Lhs {
										names = append(names, v.Name())
									}
									e7 = unsup("package-level initializer of %v reaches a method call through an interface (.%s), and a same-package method %s reads the initialized package variable %s: a HIDDEN data dependency — spec#Package_initialization leaves the initialization order unspecified there, and the realized go/types InitOrder is KNOWN to differ from gc's on this shape (latitude E7; deviation record init/hidden-dep-order) — fail closed", names, fun.Sel.Name, fun.Sel.Name, varName)
								}
								return true
							}
							if fnObj, isFn := sel.Obj().(*types.Func); isFn && !seen[fnObj] {
								seen[fnObj] = true
								if db, ok := bodies[fnObj]; ok {
									work = append(work, workItem{db.body, db.unit})
								}
							}
						} else if obj := it.unit.info.Uses[fun.Sel]; obj != nil {
							// Qualified reference (pkg.F) — no Selection.
							if fn, isFn := obj.(*types.Func); isFn && !seen[fn] {
								seen[fn] = true
								if db, ok := bodies[fn]; ok {
									work = append(work, workItem{db.body, db.unit})
								}
							}
						}
					}
					return true
				})
			}
			if e7 != nil {
				if allowHiddenDepInitOrder {
					fmt.Fprintf(os.Stderr, "nativefrontend: WARNING (E7 allow active): %v\n", e7)
					continue
				}
				return e7
			}
		}
	}
	return nil
}
