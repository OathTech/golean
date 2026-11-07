package main

// hiddendep.go — the E7 fail-closed hidden-dependency-shape detector
// (t1-fidelity-fixes, 2026-08-31; the charter-era E7 ruling ordered
// this interim guard to ship FIRST — docs/2026-08-11_latitude-inventory.md
// §E7 — and it never had until then; the REACH and OBSERVABLE
// conditions re-cut at BUG-340's fix round, 2026-11-05; the OBSERVABLE
// cut's question corrected and REACH extended to instantiated generic
// methods by lane frontend/fix-e7-cut-1107, 2026-11-07).
//
// THE HOLE IT CLOSES. spec#Package_initialization: "If other, hidden,
// data dependencies exists between variables, the initialization order
// between those variables is unspecified." The frontend realizes
// go/types' InitOrder, and so does gc (the noder writes types2's
// InitOrder — the same analysis); what differs is
// cmd/compile/internal/staticinit, which FOLDS every static initializer
// (`var y = 4`, `var y = [3]int{…}`, `var y = &z`, …) into the data
// section, so an initializer that reads y through a channel the
// dependency analysis cannot see finds y IN PLACE under gc and still
// ZERO on the machine, which assigns y at its InitOrder position (the
// S19 sweep's measurement, 2026-10-27, BUG-340: gc 454, the machine 54;
// with a DYNAMIC target — `var y = mark(1)` — nothing folds and the two
// sides agree). The deviation pin init/hidden-dep-order is that shape.
// Until this detector, any such program lowered without complaint and
// silently realized an order that does not transfer to gc — the
// census's worst live combination (soundness-direction, silent, cheap
// to guard; assessment A1-15).
//
// THE PREDICATE (fires only when the divergence is OBSERVABLE, not on
// mere presence of an interface call — the design constraint on this
// guard):
//
//  1. REACH: a kept (non-quarantined) package-level initializer's
//     expression, or a function/method/func-literal body it reaches
//     through STATICALLY-RESOLVED references — every *types.Func the
//     walk meets is followed, in call position or as a value, the
//     worklist discipline condition 2 has had since 2026-09-01 —
//     contains a selection go/types resolves to an INTERFACE METHOD
//     (the selected *types.Func's receiver is an interface type): a
//     call through an interface value; an interface method VALUE
//     (`var mv = I(T{}).m`, called by a later initializer); a method
//     EXPRESSION on an interface type (`I.m`); an interface method
//     PROMOTED through struct embedding (`S{T{}}.m()`, `(&S{…}).m()`:
//     the receiver is the struct, the method the body-less interface
//     member); a call on a TYPE PARAMETER whose constraint carries the
//     method (`func f[X I](x X) { x.m() }`). Dispatch through an
//     interface is precisely what the reference-based dependency
//     analysis cannot see through — the hidden-dep channel of the
//     spec's own example. (Before BUG-340 the condition keyed on a
//     CallExpr whose Fun was an interface-RECEIVER MethodVal selection:
//     the value, expression and promoted routes lowered unguarded —
//     the S19 sweep's two red rows plus the method-expression and
//     pointer-embedding cells of the fix lane's probes — and the
//     type-parameter route fired only by the accident that go/types'
//     Underlying of a type parameter is its constraint interface.)
//  2. OBSERVABLE: some method with the dispatched NAME, declared in
//     the SAME UNIT as the initializer, references — directly or
//     TRANSITIVELY through statically-resolved references (audit fix
//     round 2026-09-01, which found the shipped direct-read-only gate
//     DEFEATED by one helper-function indirection) — a package-level
//     variable of that unit with a kept initializer of which gc MAY
//     WRITE ANY PART ahead of its InitOrder position: a constant, or a
//     MAYBE-STATIC shape on the classifier's TARGET question
//     (staticinit.go targetFoldKindsOf, foldAnyPart; the loader's
//     targetFoldKinds). A target is excluded only when its initializer
//     has NO static path at the top level — a call to a multi-statement
//     body, arithmetic, an index or field read, a receive, a map
//     literal, a tuple: StaticAssign returns false for the shape, the
//     whole value is assigned at its InitOrder position on BOTH sides,
//     and a hidden read finds the same zero there, so the shape lowers
//     (the S19 sweep's dynamic-target twins agree; BUG-340's fix round).
//     A composite or pointer literal and a conversion to an interface
//     are foldable WHATEVER their operands: gc writes the static
//     elements, the slice header, the literal's pointer and the itab
//     word into the data section and emits only the failing elements
//     as dynamic statements (sched.go StaticAssign, the OARRAYLIT /
//     OSTRUCTLIT / OSLICELIT / OPTRLIT / OCONVIFACE cases), so
//     `var y = S{a: 1, b: g()}` has `y.a == 1` in place under gc while
//     the machine's y is still zero (the pre-merge audit of 2026-11-07:
//     gc 1013, the machine 13; `[]int{1, g()}` 2202 / 2; `&S{a: 1, b:
//     g()}` 113 / 713 — the fix round of 2026-11-05 had read the
//     BUG-061 NODE question, "does work remain", as this one and lowered
//     these silently; lane frontend/fix-e7-cut-1107). Only a foldable
//     target can reorder an observable initialization (methods of OTHER
//     units read their own unit's variables, and dependency units are
//     fully initialized before this unit's variables start — the program
//     schedule fixes cross-unit order).
//
// Within their stated scope both conditions over-approximate in the
// sound direction: a static reach that never executes, a name-matched
// method the dynamic dispatch can never select, or a foldable target gc
// happens not to fold (staticinit's seenMutation, go.dev/issue/51913)
// produces a REFUSAL of a program the machine could have run — visible,
// never wrong. The WORK side of the target test rests on the
// classifier's reading of gc; its residual risk (a shape called WORK
// where gc writes a part) is that file's, and is BUG-341's class.
//
// RECORDED RESIDUAL (deliberate scope boundary, not an oversight): a
// call through a FUNCTION VALUE the walk cannot resolve (`var f func();
// f()`, a func-typed field or parameter) is followed nowhere — covering
// it syntactically would flag every closure call inside the injected
// stdlib shims. The interface dispatch such a value carries is seen
// where the value is MADE — the initializer or body that names the
// function or takes the method value — which is where this walk
// follows it.
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

// interfaceRoute names the selection shape an interface method was
// reached by, for the refusal text: the five routes of the file
// comment's condition 1. `called` says the selection is a call's callee.
func interfaceRoute(sel *types.Selection, called bool) string {
	if sel.Kind() == types.MethodExpr {
		return "a method expression on the interface type"
	}
	if _, tp := types.Unalias(sel.Recv()).(*types.TypeParam); tp {
		return "a call on a type parameter constrained by the interface"
	}
	if !types.IsInterface(sel.Recv()) {
		if called {
			return "promoted through an embedded interface field"
		}
		return "a method value promoted through an embedded interface field"
	}
	if called {
		return "a direct call"
	}
	return "a method value escaping into the initializer"
}

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
		// Kept initialized package-level variables of this unit of which
		// gc MAY write a part ahead of its InitOrder position — the
		// observable targets. A target with NO static path at the top
		// level is assigned whole at its InitOrder position under gc as
		// under the machine: nothing in place early, no divergence, not
		// a target (file comment, condition 2). The classification is the
		// loader's on the TARGET question (staticinit.go
		// targetFoldKindsOf, foldAnyPart — not the BUG-061 node question);
		// an entry it did not classify counts as foldable — fail closed.
		initVars := map[types.Object]bool{}
		for _, ini := range u.info.InitOrder {
			if e.quarantinedInits[ini.Rhs] {
				continue
			}
			if kind, known := u.targetFoldKinds[ini.Rhs]; known && kind == initWork {
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
		// name — some same-unit method of that name references a
		// foldable initialized package variable of this unit, DIRECTLY
		// or TRANSITIVELY through statically-resolved references (the
		// same worklist discipline as the reach walk below). Every
		// *types.Func the body references is followed (call positions,
		// method selectors, method/func values alike): following a
		// function the dynamic path never runs can only
		// over-approximate in the sound direction. Calls through
		// function VALUES stay unfollowed — the recorded residual.
		methodReadsInitVar := func(name string) (string, bool) {
			work := append([]declBody{}, methodsByName[name]...)
			seen := map[types.Object]bool{}
			for len(work) > 0 {
				mb := work[0]
				work = work[1:]
				var hit string
				ast.Inspect(mb.body, func(n ast.Node) bool {
					if hit != "" {
						return false
					}
					if id, ok := n.(*ast.Ident); ok {
						obj := mb.unit.info.Uses[id]
						if obj == nil {
							return true
						}
						if initVars[obj] {
							hit = obj.Name()
							return false
						}
						if fn, isFn := obj.(*types.Func); isFn {
							// An instantiated generic method's object is the
							// instance's; its body is the origin's (bodies is
							// keyed by Defs). Origin is the identity for a
							// non-generic function.
							fn = fn.Origin()
							if !seen[fn] {
								seen[fn] = true
								if db, ok := bodies[fn]; ok {
									work = append(work, db)
								}
							}
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
			follow := func(fn *types.Func) {
				// A method of an instantiated generic type (`G[int]{}.M()`)
				// resolves to the INSTANCE's *types.Func, which bodies — keyed
				// by the declarations' Defs objects — does not hold; its body
				// is the origin's (pre-merge audit 2026-11-07, finding 2: the
				// stenciled method's hidden read was followed nowhere, gc 44,
				// the machine 4). Origin is the identity for a non-generic
				// function, so the key is always the declaration's.
				fn = fn.Origin()
				if seen[fn] {
					return
				}
				seen[fn] = true
				if db, ok := bodies[fn]; ok {
					work = append(work, workItem{db.body, db.unit})
				}
			}
			var e7 error
			for len(work) > 0 && e7 == nil {
				it := work[0]
				work = work[1:]
				// The callee positions of this node, so the refusal can
				// name the route (a call vs. an escaping value).
				callees := map[ast.Node]bool{}
				ast.Inspect(it.node, func(n ast.Node) bool {
					if call, ok := n.(*ast.CallExpr); ok {
						callees[ast.Unparen(call.Fun)] = true
					}
					return true
				})
				ast.Inspect(it.node, func(n ast.Node) bool {
					if e7 != nil {
						return false
					}
					switch x := n.(type) {
					case *ast.Ident:
						// Every function or method the node names, in
						// any position (a call, a value, a method value's
						// or method expression's Sel, a qualified pkg.F):
						// its body joins the walk. An interface method
						// has no body and is judged at its selector.
						if fn, isFn := it.unit.info.Uses[x].(*types.Func); isFn {
							follow(fn)
						}
					case *ast.SelectorExpr:
						sel, ok := it.unit.info.Selections[x]
						if !ok {
							return true // a qualified reference: its Sel ident is followed above
						}
						fn, isFn := sel.Obj().(*types.Func)
						if !isFn {
							return true // a field
						}
						if _, iface := recvInterface(fn); !iface {
							return true // a concrete method: followed at x.Sel
						}
						// The hidden-dep channel: the selected method is an
						// interface's, on any of the file comment's routes.
						// Fire only if observable: a method of this name in
						// the INITIALIZER's unit reads a foldable initialized
						// var of that unit. (The selection may sit in a
						// reached body of ANOTHER unit, but the initializer
						// unit's types flow anywhere, so the gate is always
						// the initializer unit's.)
						if varName, obs := methodReadsInitVar(x.Sel.Name); obs {
							names := make([]string, 0, len(ini.Lhs))
							for _, v := range ini.Lhs {
								names = append(names, v.Name())
							}
							e7 = unsup("package-level initializer of %v reaches a method call through an interface (.%s: %s), and a same-package method %s reads the initialized package variable %s, whose initializer gc may fold into the data section: a HIDDEN data dependency — spec#Package_initialization leaves the initialization order unspecified there, and the realized go/types InitOrder is KNOWN to differ from gc's on this shape (latitude E7; deviation record init/hidden-dep-order) — fail closed", names, x.Sel.Name, interfaceRoute(sel, callees[x]), x.Sel.Name, varName)
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
