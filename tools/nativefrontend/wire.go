package main

// wire.go emits the native wire schema: a typed Go AST (Go's grammar with
// go/types types attached and names resolved). The Lean side
// (GoLean/NativeJson.lean + NativeToIR.lean) decodes it strictly and lowers it
// to GoCore. Keeping the wire a faithful typed Go AST — rather than
// pre-desugared GoCore — keeps this emitter a mechanical serializer and
// concentrates the semantic GoCore mapping in Lean, which stays authoritative
// and extends one construct at a time.

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
)

// emitter walks a type-checked package and produces wire nodes (Go values
// ready for JSON encoding: map[string]any / []any / scalars).
type emitter struct {
	fset *token.FileSet
	info *types.Info
	pkg  *types.Package

	// A-normal form: calls and allocations in expression position are hoisted
	// into let-bound temp statements accumulated here for the statement being
	// emitted, so GoCore expressions stay pure (calls are statements).
	hoisted        []any
	tmpSeq         int
	hoistForbidden string // non-empty where hoisting is unsafe (short-circuit RHS, loop cond)

	// Lambda lifting (W5, docs/2026-07-24_sequential-coverage-scoping.md §8):
	// func literals are hoisted to synthetic top-level functions taking their
	// captured variables as POINTER parameters, so Go's capture-by-reference
	// is explicit in the lowering. `lifted` accumulates them; `captureParam`
	// maps a captured variable to its pointer-parameter name while emitting a
	// lifted body, so references to it become derefs.
	lifted       []any
	liftSeq      int
	curFuncName  string
	captureParam map[types.Object]string
	// The enclosing function's result tuple, for the return-site
	// interface-conversion wrap.
	curResults *types.Tuple

	// Whether the `defer recover()` no-op function has been registered.
	deferNoopEmitted bool

	// Label usage of the CURRENT function body (control-flow slice,
	// docs/2026-08-04_control-flow-design.md), computed by scanLabelUses
	// before the body is emitted and saved/restored around nested func
	// literals (a label's scope never crosses a function boundary):
	// labels referenced by labeled break/continue, and by goto.
	branchLabels map[string]bool
	gotoLabels   map[string]bool

	// Goto dispatch context (stage 3, emitGotoBody): segment index per
	// top-level goto-target label, the program-counter variable, and the
	// dispatch loop's machine label. A `goto` lowers to
	// `$pc = seg(L); continue-to $gotoN`. Nil outside a restructured
	// body, so a goto with no context fails closed.
	gotoSeg  map[string]int
	gotoPC   string
	gotoLoop string

	// Function-LOCAL type declarations (`type T ...` in a body): they
	// register in the global type table (type declarations have no
	// runtime effect — legal for goto to jump over), with a program-wide
	// duplicate-TypeId refusal in emitProgram.
	localTypeDefs     []any
	localIfaceMethods []any

	// Interface-receiver methods CALLED somewhere in the package, keyed
	// "<IfaceName>.<Method>" (the exact func id the call emits). Interfaces
	// declared in the package anchor their methods via emitGenDeclTypes;
	// predeclared ones (error) and, later, imported ones have no decl here,
	// so emitProgram synthesizes their table entries from this record.
	calledIfaceMethods map[string]calledIfaceMethod

	// EVERY interface type that reaches the wire, keyed by its wire name.
	// Recorded at the single type choke point (emitType) plus the
	// declaration loop, so an interface referenced only as an assert TARGET
	// is captured too. emitProgram turns each into an `interface` TypeDef
	// carrying the FULL method set — the machine's interface-satisfaction
	// requirements. Before this, requirements were derived from the DISPATCH
	// table, which holds only methods actually CALLED, so an interface with
	// no call site had an EMPTY requirement list and every dynamic type
	// vacuously satisfied it (pre-merge audit 2026-07-31, finding 0).
	seenInterfaces map[string]*types.Interface

	// Every NAMED STRUCT type declared in the package (package-level and
	// function-local), collected by emitGenDeclTypes for the promotion
	// wrapper pass (design note 2026-08-05 D1.3): emitProgram synthesizes
	// forwarding wrappers for each promoted entry of the type's method
	// set, so the machine's flat method table is COMPLETE and a missing
	// method is real information (D2).
	namedStructTypes []*types.Named

	// Every IMPORTED named non-interface type whose identity reached the
	// wire (design note 2026-08-05 D5): emitProgram emits, per type whose
	// EXPORTED method set is fully emittable, an `unsupported`-marker
	// TypeDef (existence only — structural use keeps failing closed) plus
	// signature-carrying method STUBS, so interface satisfaction can
	// answer instead of refusing (BUG-009's polarity).
	importedNamed map[string]*types.Named

	// Mangled instantiation key → the types.Type it names (mono.go, the
	// generics slice): the belt-and-suspenders collision registry behind
	// the mangling injectivity argument, capped at monoRegistryCap. Every
	// mangled key passes through registerMangledKey exactly once per
	// spelling.
	mangledKeys map[string]types.Type

	// Monomorphization state (mono.go, generics design note 2026-08-05).
	// curSubst is the ACTIVE stencil substitution (declaration type
	// parameter → concrete argument), nil outside stenciling; substErr
	// records the first substitution failure surfaced as an Invalid type
	// (emitType refuses on it — fail closed). genericFuncDecls maps each
	// generic function object to its declaration for the worklist;
	// funcInsts/funcInstQueue are the dedup map and pending queue of
	// stencils; monoCtxt is the shared types.Instantiate context.
	curSubst         map[*types.TypeParam]types.Type
	// curTargs mirrors curSubst as the ORDERED argument list of the
	// active instantiation (nil outside stenciling) — consumed by
	// qualifiedTypeName to parameterize TypeIds of function-local type
	// declarations (arc-final audit F3).
	curTargs []types.Type
	substErr         error
	genericFuncDecls map[*types.Func]*ast.FuncDecl
	funcInsts        map[string]*funcInstWork
	funcInstQueue    []*funcInstWork
	monoCtxt         *types.Context
	// Method declarations on GENERIC types, keyed by the receiver's
	// ORIGIN named type: skipped by the declaration loop (a generic
	// method has no uninstantiated runtime form) and stenciled per
	// receiver instantiation (flushTypeInsts).
	genericMethodDecls map[*types.Named][]*ast.FuncDecl
	// Instantiated-type declarations: dedup map + pending queue of
	// TypeDef/method stencils, one per mangled TypeId that reaches the
	// wire (instTypeIdForWire).
	typeInsts     map[string]*typeInstWork
	typeInstQueue []*typeInstWork
	// Journal of every mono registration, for the per-decl quarantine
	// rollback (audit response m5; see rollbackMono).
	monoLog []monoLogEntry

	// Every package NAME that qualified a wire TypeId, mapped to the
	// distinct import PATHs that used it. Go keys type identity on the
	// path, the wire key on the name, so a name reached by two paths means
	// two distinct Go types share one TypeId — `checkPackageNameCollisions`
	// fails the export closed on that (pre-merge audit 2026-07-31,
	// findings 4/7).
	qualPkgPaths map[string][]string

	// Package-level variables (init slice, docs/2026-08-05_init-design.md):
	// `collectGlobals` is the SINGLE place gids come from — a dense index
	// per package-scope *types.Var in declaration order (files in lexical
	// filename order), matching the driver's seeding of cell gid at
	// Loc.base(gid). Blank package-level vars have no cell and no gid
	// (their initializers still run via InitOrder). `globalInitStmt` maps
	// each initializer's RHS expression to a fabricated assignment whose
	// Lhs are the ORIGINAL declaring idents, so `$pkginit` synthesis
	// reuses the ordinary emitAssign machinery (hoists, interface boxing,
	// multi-value calls, blank targets). `initFuncNames` are the mangled
	// `$initN` ids of the package's init() functions, source order.
	globalVars     map[*types.Var]int
	globalDefs     []any
	globalInitStmt map[ast.Expr]*ast.AssignStmt
	initFuncNames  []string
}

// noteInterface records an interface type for the `interface` TypeDef pass.
// The canonical EMPTY interface (`any`) is excluded on purpose: it is
// satisfied by every type BY DESIGN in the machine (Go's `any`), so it needs
// no declaration — and keeping it off the wire keeps `any`-using programs'
// lowering unchanged.
// FIRST-time registrations are journaled for the quarantine rollback
// (delta-review R1): an interface noted only by a refused body must not
// survive into the declaration pass, whose failure (an unsupported
// method signature) refuses the WHOLE export. Re-notes of an existing
// name are not journaled, so a rollback never deletes an entry a
// SUCCESSFUL declaration also owns.
func (e *emitter) noteInterface(name string, iface *types.Interface) {
	if name == emptyInterfaceName {
		return
	}
	// Record the interface AT THE ACTIVE INSTANTIATION (arc-final audit
	// F5, 2026-08-06): the wire NAME is substitution-aware
	// (ifaceWireName), but a dispatch through a generic interface used
	// at the enclosing function's type parameter hands this the ORIGIN
	// interface, whose method signatures still mention T — the
	// declaration pass then emits them with curSubst cleared and refuses
	// the WHOLE export ("type parameter T outside an instantiation").
	// Substituting here keys the substituted method set under the
	// substituted name. applySubst is identity outside stenciling; a
	// substitution failure keeps the origin (fail-closed downstream).
	if e.curSubst != nil {
		savedErr := e.substErr
		if sub, ok := types.Unalias(e.applySubst(iface)).(*types.Interface); ok {
			iface = sub
		}
		// A failed attempt keeps the origin (the declaration pass then
		// refuses loudly on the unsubstituted signature, as before) and
		// must not poison substErr for unrelated emission.
		e.substErr = savedErr
	}
	if e.seenInterfaces == nil {
		e.seenInterfaces = map[string]*types.Interface{}
	}
	if _, seen := e.seenInterfaces[name]; !seen {
		e.monoLog = append(e.monoLog, monoLogEntry{monoLogSeenIface, name})
	}
	e.seenInterfaces[name] = iface
}

// noteCalledIfaceMethod records one interface-dispatch call target (the
// anchor-synthesis input), journaled like noteInterface (delta-review
// R1): a dispatch recorded only by a refused body must not force a
// synthesized anchor whose signature emission would refuse the export.
func (e *emitter) noteCalledIfaceMethod(key string, cm calledIfaceMethod) {
	if e.calledIfaceMethods == nil {
		e.calledIfaceMethods = map[string]calledIfaceMethod{}
	}
	if _, seen := e.calledIfaceMethods[key]; !seen {
		e.monoLog = append(e.monoLog, monoLogEntry{monoLogCalledIface, key})
	}
	e.calledIfaceMethods[key] = cm
}

// calledIfaceMethod records one interface-dispatch call target: the receiver
// interface's wire name (qualified, or bare for predeclared), the method
// name, and its signature (for params/results of a synthesized table entry).
type calledIfaceMethod struct {
	ifaceName string
	method    string
	sig       *types.Signature
	// The stencil substitution ACTIVE at the call site (nil outside an
	// instantiation). The recorded sig is the ORIGIN method's — for a
	// generic interface used at the enclosing function's type parameter
	// (`gipVisitor[T].Visit` inside `gipApply[T]`) it still mentions T,
	// while the KEY is substitution-aware; the anchor pass must emit the
	// signature under THIS substitution, not with curSubst cleared
	// (arc-final audit F5, 2026-08-06: the un-substituted emission
	// refused the WHOLE export with "type parameter T outside an
	// instantiation", poisoning unrelated subjects in the package).
	subst map[*types.TypeParam]types.Type
}

// emptyStructName is the canonical GoCore type name for the empty struct
// struct{} (the set-value idiom map[K]struct{}).
const emptyStructName = "struct{}"

// emptyInterfaceName is the canonical GoCore type name for the empty interface
// (`any` / `interface{}`) — the one interface the machine satisfies by design.
const emptyInterfaceName = "any"

// unsupported is returned when a construct is not yet modeled. The pipeline
// fails closed: the emitter never approximates.
type unsupported struct{ what string }

func (u unsupported) Error() string { return "native frontend unsupported: " + u.what }

func unsup(format string, args ...any) error {
	return unsupported{fmt.Sprintf(format, args...)}
}

// ---- types ----

func (e *emitter) emitType(t types.Type) (any, error) {
	// The single type choke point applies the ACTIVE stencil substitution
	// (mono.go): every wire type inside a stencil is emitted at the
	// current instantiation. Identity outside stenciling.
	if e.curSubst != nil {
		t = e.applySubst(t)
	}
	switch ty := t.(type) {
	case *types.Basic:
		if ty.Kind() == types.Invalid && e.substErr != nil {
			// applySubst surfaced a substitution failure as Invalid;
			// report the recorded cause, not a generic message.
			return nil, e.substErr
		}
		return e.emitBasic(ty)
	case *types.Alias:
		// Aliases — generic ones included (gotypesalias=1, G4) — are
		// IDENTITY-TRANSPARENT (spec §Alias declarations; design-note
		// §3.2 "aliases never mint TypeIds"): the wire sees the aliased
		// type directly, e.g. aliasSlice[int] emits as []int.
		return e.emitType(types.Unalias(ty))
	case *types.TypeParam:
		// Reachable only OUTSIDE a stencil (inside one, applySubst above
		// either resolves it or records substErr): a generic declaration
		// being emitted un-instantiated — fail closed (this is also the
		// per-decl quarantine trigger for generic declarations).
		return nil, unsup("type parameter %s outside an instantiation", ty)
	case *types.Named:
		if ty.TypeArgs().Len() > 0 {
			return e.emitInstantiatedNamed(ty)
		}
		obj := ty.Obj()
		// A named type whose underlying is an interface is an interface type;
		// otherwise it is a defined type. GoCore distinguishes the two. Names
		// are package-qualified ("main.T"); predeclared types (error) stay
		// bare (no package).
		if iface, ok := ty.Underlying().(*types.Interface); ok {
			name := e.qualifiedTypeName(obj)
			e.noteInterface(name, iface)
			return map[string]any{"kind": "interface", "name": name}, nil
		}
		qname := e.qualifiedTypeName(obj)
		if obj.Pkg() != nil && obj.Pkg() != e.pkg {
			// An imported concrete named type: record it for the
			// method-set stub pass (D5).
			if e.importedNamed == nil {
				e.importedNamed = map[string]*types.Named{}
			}
			e.importedNamed[qname] = ty
		}
		return map[string]any{"kind": "named", "name": qname}, nil
	case *types.Pointer:
		elem, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "pointer", "elem": elem}, nil
	case *types.Slice:
		elem, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "slice", "elem": elem}, nil
	case *types.Array:
		elem, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "array", "len": ty.Len(), "elem": elem}, nil
	case *types.Map:
		key, err := e.emitType(ty.Key())
		if err != nil {
			return nil, err
		}
		val, err := e.emitType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "map", "key": key, "value": val}, nil
	case *types.Interface:
		if ty.Empty() {
			return map[string]any{"kind": "interface", "name": emptyInterfaceName}, nil
		}
		// Anonymous non-empty interface (a `case interface{ M() }`, an
		// assert target, a variable type): canonical wire name from the
		// type's own rendering — SOUND because Go interface identity is
		// structural, so structurally identical spellings are one type
		// (design note 2026-08-05 D3). Qualified with package NAMES like
		// every other TypeId (the package-name collision check covers the
		// same hazard class). Registered like named interfaces, so the
		// declaration pass emits its full method set.
		if !ty.IsMethodSet() {
			return nil, unsup("non-method-set interface type %s (type constraints are not interface values)", ty)
		}
		name := types.TypeString(ty, func(p *types.Package) string { return p.Name() })
		e.noteInterface(name, ty)
		return map[string]any{"kind": "interface", "name": name}, nil
	case *types.Signature:
		params := []any{}
		for i := 0; i < ty.Params().Len(); i++ {
			pt, err := e.emitType(ty.Params().At(i).Type())
			if err != nil {
				return nil, err
			}
			params = append(params, pt)
		}
		results := []any{}
		for i := 0; i < ty.Results().Len(); i++ {
			rt, err := e.emitType(ty.Results().At(i).Type())
			if err != nil {
				return nil, err
			}
			results = append(results, rt)
		}
		return map[string]any{"kind": "func", "params": params, "results": results}, nil
	case *types.Struct:
		// The empty struct struct{} (the set-value idiom map[K]struct{}) is a
		// canonical named empty struct in GoCore; other anonymous structs are
		// not modeled.
		if ty.NumFields() == 0 {
			return map[string]any{"kind": "named", "name": emptyStructName}, nil
		}
		return nil, unsup("anonymous non-empty struct type %s", ty)
	default:
		return nil, unsup("type %T (%s)", t, t)
	}
}

func (e *emitter) emitBasic(b *types.Basic) (any, error) {
	switch b.Kind() {
	case types.Bool:
		return map[string]any{"kind": "bool"}, nil
	case types.String:
		return map[string]any{"kind": "string"}, nil
	case types.Int:
		return intType("int"), nil
	case types.Int8:
		return intType("int8"), nil
	case types.Int16:
		return intType("int16"), nil
	case types.Int32:
		return intType("int32"), nil
	case types.Int64:
		return intType("int64"), nil
	case types.Uint:
		return intType("uint"), nil
	case types.Uint8:
		return intType("uint8"), nil
	case types.Uint16:
		return intType("uint16"), nil
	case types.Uint32:
		return intType("uint32"), nil
	case types.Uint64:
		return intType("uint64"), nil
	case types.Uintptr:
		return intType("uintptr"), nil
	case types.Float32:
		return floatType("float32"), nil
	case types.Float64:
		return floatType("float64"), nil
	// Untyped constants carry their default type at use sites; go/types has
	// usually already resolved them, but guard the bare kinds.
	case types.UntypedInt:
		return intType("int"), nil
	case types.UntypedFloat:
		// The spec's default type for an untyped float constant.
		return floatType("float64"), nil
	case types.UntypedBool:
		return map[string]any{"kind": "bool"}, nil
	case types.UntypedString:
		return map[string]any{"kind": "string"}, nil
	default:
		return nil, unsup("basic type %s", b)
	}
}

func intType(kind string) map[string]any {
	return map[string]any{"kind": "int", "int": kind}
}

func floatType(kind string) map[string]any {
	return map[string]any{"kind": "float", "float": kind}
}

// emitInstantiatedNamed is the wire arm for INSTANTIATED generic named
// types (mono.go): the type names by its mangled key, and its TypeDef —
// with the full stenciled method set — is enqueued for emission from the
// instantiation worklist. Instantiated INTERFACES need no TypeDef stencil
// of their own: go/types' instance Underlying() carries the substituted
// method set, and the seenInterfaces declaration pass emits it like any
// other interface (satisfaction requirements), with dispatch anchors
// synthesized from recorded calls.
func (e *emitter) emitInstantiatedNamed(ty *types.Named) (any, error) {
	if mentionsTypeParam(ty, nil) {
		return nil, unsup("instantiated type %s still mentions a type parameter", ty)
	}
	if iface, isIface := ty.Underlying().(*types.Interface); isIface {
		if !iface.IsMethodSet() {
			return nil, unsup("constraint interface %s used as a value type", ty)
		}
		key, err := e.instTypeId(ty)
		if err != nil {
			return nil, err
		}
		e.noteInterface(key, iface)
		return map[string]any{"kind": "interface", "name": key}, nil
	}
	key, err := e.instTypeIdForWire(ty)
	if err != nil {
		return nil, err
	}
	return map[string]any{"kind": "named", "name": key}, nil
}

// typeOf returns the emitted wire type of an expression from go/types.
func (e *emitter) typeOf(expr ast.Expr) (any, error) {
	tv, ok := e.info.Types[expr]
	if !ok {
		if id, isID := expr.(*ast.Ident); isID {
			if obj := e.info.ObjectOf(id); obj != nil {
				return e.emitType(obj.Type())
			}
		}
		return nil, unsup("no type for expression %T at %s", expr, e.fset.Position(expr.Pos()))
	}
	return e.emitType(tv.Type)
}
