package main

// mono.go — frontend monomorphization (generics slice, design note
// docs/2026-08-05_generics-design.md; decisions of record §9). This file is
// the IDENTITY layer: mangled TypeId/FuncId construction for generic
// instantiations plus the mangled-key → types.Type registry that backstops
// the injectivity argument. THE ONE BOUNDARY CONSTRUCTOR rule (CLAUDE.md):
// every mangled instantiation key is built here and nowhere else.
//
// Key shape (§3.2, pinned by the §3.1 reflect probes and mono_test.go):
//
//	TypeId  main.Pair[main.Inner]     qualified origin + bracketed args
//	FuncId  genericAdd[int]           bare declared name + bracketed args
//	        main.box[int].Get        (methods: receiver TypeId + "." + name)
//
// Arguments render the way reflect/the runtime spell them — package-NAME
// qualifiers, "," separators with no space (types.TypeString uses ", ";
// reflect.Type.Name() does not), canonical basic names (byte→uint8,
// rune→int32), "interface {}" for the empty interface, "struct {}" for
// the empty struct — so Go panic texts contain the key VERBATIM and
// TypeId.unqualified reproduces reflect.Type.Name() (the observation
// channel's contract). SCOPE of that claim (audit response M3): it holds
// exactly on the ADMITTED argument surface; function-local defined types
// — which gc names with a compiler-internal unique suffix (main.score·1)
// no source-derived key can reproduce — are refused, not approximated.

import (
	"errors"
	"go/ast"
	"go/types"
	"strings"
)

// ---- substitution (G2: the instantiation closure) ----

// funcInstWork is one pending function stencil: the generic declaration,
// the substitution environment (declaration type parameter → concrete type
// argument), and the mangled FuncId it emits under.
type funcInstWork struct {
	mangled string
	decl    *ast.FuncDecl
	env     map[*types.TypeParam]types.Type
	// The instantiation's type arguments IN DECLARATION ORDER (the env is
	// an unordered map): the suffix source for TypeIds of types DECLARED
	// INSIDE the stencil (arc-final audit F3, 2026-08-06 — gc names a
	// local type with the enclosing instantiation's arguments,
	// reflect.Name() "box[int]").
	targs []types.Type
	// The DECLARING unit (multi-package W1.1): the stencil body's AST
	// nodes are keyed in that unit's types.Info, so emitFuncInst
	// switches e.pkg/e.info to it. Nil = the current package (direct
	// emitter construction in unit tests).
	unit *sourcePkg
}

// applySubst applies the ACTIVE stencil substitution to a type reaching a
// decision or emission point. Identity outside stenciling and for types
// that mention no type parameter. On a substitution failure it records the
// error and returns Invalid, which every downstream consumer refuses
// (emitType has an explicit Invalid arm returning the recorded error) —
// fail closed, never a silent approximation.
func (e *emitter) applySubst(t types.Type) types.Type {
	if t == nil || e.curSubst == nil || !mentionsTypeParam(t, nil) {
		return t
	}
	st, err := e.substType(t)
	if err != nil {
		if e.substErr == nil {
			e.substErr = err
		}
		return types.Typ[types.Invalid]
	}
	return st
}

// goTypeOf is the substitution-aware replacement for info.TypeOf: every
// type-driven DECISION during emission (underlying-kind switches,
// interface checks, tuple detection) must see the type at the CURRENT
// instantiation, never the raw type-parameter form.
func (e *emitter) goTypeOf(x ast.Expr) types.Type {
	return e.applySubst(e.info.TypeOf(x))
}

// typesEntry is the substitution-aware replacement for info.Types[x]:
// the TYPE is substituted, the constant VALUE is the original one —
// emission stays over the ORIGINAL types.Info (design note §4.1: a
// constant converted to a type parameter is a NON-constant, and
// re-type-checking substituted source would re-fold it; go/types encodes
// that in Value == nil, which substitution must preserve).
func (e *emitter) typesEntry(x ast.Expr) (types.TypeAndValue, bool) {
	tv, ok := e.info.Types[x]
	if ok && tv.Type != nil {
		tv.Type = e.applySubst(tv.Type)
	}
	return tv, ok
}

// mentionsTypeParam reports whether t structurally mentions any
// *types.TypeParam. Named types are entered only through their type
// ARGUMENTS (a non-generic named type cannot capture an outer parameter),
// so the walk terminates without a seen-set.
func mentionsTypeParam(t types.Type, _ map[types.Type]bool) bool {
	switch ty := t.(type) {
	case *types.TypeParam:
		return true
	case *types.Basic:
		return false
	case *types.Named:
		args := ty.TypeArgs()
		for i := 0; i < args.Len(); i++ {
			if mentionsTypeParam(args.At(i), nil) {
				return true
			}
		}
		return false
	case *types.Alias:
		return mentionsTypeParam(types.Unalias(ty), nil)
	case *types.Pointer:
		return mentionsTypeParam(ty.Elem(), nil)
	case *types.Slice:
		return mentionsTypeParam(ty.Elem(), nil)
	case *types.Array:
		return mentionsTypeParam(ty.Elem(), nil)
	case *types.Chan:
		return mentionsTypeParam(ty.Elem(), nil)
	case *types.Map:
		return mentionsTypeParam(ty.Key(), nil) || mentionsTypeParam(ty.Elem(), nil)
	case *types.Signature:
		return mentionsTypeParam(ty.Params(), nil) || mentionsTypeParam(ty.Results(), nil)
	case *types.Tuple:
		for i := 0; i < ty.Len(); i++ {
			if mentionsTypeParam(ty.At(i).Type(), nil) {
				return true
			}
		}
		return false
	case *types.Struct:
		for i := 0; i < ty.NumFields(); i++ {
			if mentionsTypeParam(ty.Field(i).Type(), nil) {
				return true
			}
		}
		return false
	case *types.Interface:
		// Anonymous interfaces mentioning a type parameter in a method
		// signature are conservatively reported (substType then refuses);
		// constraint interfaces never reach emission.
		for i := 0; i < ty.NumMethods(); i++ {
			if mentionsTypeParam(ty.Method(i).Type(), nil) {
				return true
			}
		}
		return false
	default:
		// Unknown shapes: report a mention so substType refuses loudly
		// rather than silently passing an unsubstituted type through.
		return true
	}
}

// substType substitutes the active environment into t. Named/Alias
// instantiations route through types.Instantiate — go/types' own subster —
// with a small structural walker for the composite shells (note §8 G2:
// prefer keeping substitution inside go/types wherever the API allows).
func (e *emitter) substType(t types.Type) (types.Type, error) {
	switch ty := t.(type) {
	case *types.TypeParam:
		sub, ok := e.curSubst[ty]
		if !ok {
			return nil, unsup("unbound type parameter %s during instantiation", ty)
		}
		return sub, nil
	case *types.Basic:
		return ty, nil
	case *types.Named:
		args := ty.TypeArgs()
		if args.Len() == 0 {
			return ty, nil
		}
		newArgs := make([]types.Type, args.Len())
		changed := false
		for i := 0; i < args.Len(); i++ {
			sub, err := e.substType(args.At(i))
			if err != nil {
				return nil, err
			}
			if sub != args.At(i) {
				changed = true
			}
			newArgs[i] = sub
		}
		if !changed {
			return ty, nil
		}
		inst, err := types.Instantiate(e.instCtxt(), ty.Origin(), newArgs, false)
		if err != nil {
			return nil, unsup("instantiate %s: %v", ty.Origin(), err)
		}
		return inst, nil
	case *types.Alias:
		// Aliases are identity-transparent (§3.2): substitute the aliased
		// type; the alias name never reaches the wire.
		return e.substType(types.Unalias(ty))
	case *types.Pointer:
		elem, err := e.substType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return types.NewPointer(elem), nil
	case *types.Slice:
		elem, err := e.substType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return types.NewSlice(elem), nil
	case *types.Array:
		elem, err := e.substType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return types.NewArray(elem, ty.Len()), nil
	case *types.Chan:
		elem, err := e.substType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return types.NewChan(ty.Dir(), elem), nil
	case *types.Map:
		key, err := e.substType(ty.Key())
		if err != nil {
			return nil, err
		}
		val, err := e.substType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return types.NewMap(key, val), nil
	case *types.Signature:
		params, err := e.substTuple(ty.Params())
		if err != nil {
			return nil, err
		}
		results, err := e.substTuple(ty.Results())
		if err != nil {
			return nil, err
		}
		return types.NewSignatureType(nil, nil, nil, params, results, ty.Variadic()), nil
	case *types.Tuple:
		return e.substTuple(ty)
	case *types.Struct:
		fields := make([]*types.Var, ty.NumFields())
		tags := make([]string, ty.NumFields())
		for i := 0; i < ty.NumFields(); i++ {
			f := ty.Field(i)
			ft, err := e.substType(f.Type())
			if err != nil {
				return nil, err
			}
			fields[i] = types.NewField(f.Pos(), f.Pkg(), f.Name(), ft, f.Anonymous())
			tags[i] = ty.Tag(i)
		}
		return types.NewStruct(fields, tags), nil
	case *types.Interface:
		if !mentionsTypeParam(ty, nil) {
			return ty, nil
		}
		// An interface whose METHOD SIGNATURES mention a type parameter
		// (the origin interface of a generic-interface dispatch,
		// arc-final audit F5, 2026-08-06 — previously refused outright):
		// substitute each method signature. Embedded type-set
		// constraints never reach emission; refuse rather than guess.
		if ty.NumEmbeddeds() > 0 {
			return nil, unsup("interface with embedded constraints mentioning a type parameter (%s)", ty)
		}
		fns := make([]*types.Func, ty.NumMethods())
		for i := 0; i < ty.NumMethods(); i++ {
			m := ty.Method(i)
			sub, err := e.substType(m.Type())
			if err != nil {
				return nil, err
			}
			sig, ok := sub.(*types.Signature)
			if !ok {
				return nil, unsup("interface method substitution produced non-signature for %s", m.Name())
			}
			fns[i] = types.NewFunc(m.Pos(), m.Pkg(), m.Name(), sig)
		}
		ni := types.NewInterfaceType(fns, nil)
		ni.Complete()
		return ni, nil
	default:
		return nil, unsup("substitution into %T (%s)", t, t)
	}
}

func (e *emitter) substTuple(t *types.Tuple) (*types.Tuple, error) {
	vars := make([]*types.Var, t.Len())
	for i := 0; i < t.Len(); i++ {
		v := t.At(i)
		vt, err := e.substType(v.Type())
		if err != nil {
			return nil, err
		}
		vars[i] = types.NewVar(v.Pos(), v.Pkg(), v.Name(), vt)
	}
	return types.NewTuple(vars...), nil
}

// instCtxt is the shared instantiation context: types.Instantiate
// deduplicates identical instantiations through it, so repeated
// substitution yields pointer-shared (and always Identical) instances.
func (e *emitter) instCtxt() *types.Context {
	if e.monoCtxt == nil {
		e.monoCtxt = types.NewContext()
	}
	return e.monoCtxt
}

// ---- the function-instantiation worklist ----

// funcInstanceAt resolves the instantiation at a use-site identifier of a
// generic function: reads the Instances entry (go/types' full inference —
// the frontend re-implements none of it), substitutes the ACTIVE stencil
// bindings into the recorded arguments (derived instantiations inside
// generic bodies mention the enclosing parameters, note §2a), mangles,
// registers the stencil work item, and returns the mangled FuncId plus
// the fully concrete instantiated signature.
func (e *emitter) funcInstanceAt(id *ast.Ident, fn *types.Func) (string, *types.Signature, error) {
	inst, ok := e.info.Instances[id]
	if !ok {
		return "", nil, unsup("generic function %s has no instantiation record at %s",
			fn.Name(), e.fset.Position(id.Pos()))
	}
	gsig, ok := fn.Type().(*types.Signature)
	if !ok {
		return "", nil, unsup("generic non-signature function %s", fn.Name())
	}
	n := inst.TypeArgs.Len()
	if n != gsig.TypeParams().Len() {
		return "", nil, unsup("instantiation arity mismatch for %s: %d args for %d params",
			fn.Name(), n, gsig.TypeParams().Len())
	}
	targs := make([]types.Type, n)
	for i := 0; i < n; i++ {
		arg := inst.TypeArgs.At(i)
		if mentionsTypeParam(arg, nil) {
			if e.curSubst == nil {
				return "", nil, unsup("free type parameter in instantiation of %s outside a stencil", fn.Name())
			}
			sub, err := e.substType(arg)
			if err != nil {
				return "", nil, err
			}
			arg = sub
		}
		targs[i] = arg
	}
	// The stencil FuncId roots at the identity-boundary wire name
	// (W1.1): a source-package generic mangles as "path.F[int]", so two
	// same-named generics in different packages stencil apart.
	mangled, err := e.instFuncId(e.funcWireName(fn), targs)
	if err != nil {
		return "", nil, err
	}
	// The concrete signature comes from types.Instantiate over the GENERIC
	// signature (not from substituting inst.Type, which mentions the
	// enclosing parameters in derived entries).
	csigT, err := types.Instantiate(e.instCtxt(), gsig, targs, false)
	if err != nil {
		return "", nil, unsup("instantiate %s%v: %v", fn.Name(), targs, err)
	}
	csig := csigT.(*types.Signature)
	if err := e.registerFuncInst(mangled, fn, targs); err != nil {
		return "", nil, err
	}
	return mangled, csig, nil
}

// registerFuncInst enqueues one stencil per distinct mangled FuncId. The
// mangled key is also entered in the collision registry against the
// instantiated signature — a FuncId collision (same rendered key, two
// non-Identical instantiations) refuses the export like a TypeId one.
func (e *emitter) registerFuncInst(mangled string, fn *types.Func, targs []types.Type) error {
	gsig := fn.Type().(*types.Signature)
	csigT, err := types.Instantiate(e.instCtxt(), gsig, targs, false)
	if err != nil {
		return unsup("instantiate %s: %v", fn.Name(), err)
	}
	if err := e.registerMangledKey(mangled, csigT); err != nil {
		return err
	}
	if _, done := e.funcInsts[mangled]; done {
		return nil
	}
	decl, ok := e.genericFuncDecls[fn]
	if !ok {
		return unsup("generic function %s has no declaration in this package (imported generics are not modeled)", fn.Name())
	}
	env := map[*types.TypeParam]types.Type{}
	for i := 0; i < gsig.TypeParams().Len(); i++ {
		env[gsig.TypeParams().At(i)] = targs[i]
	}
	if e.funcInsts == nil {
		e.funcInsts = map[string]*funcInstWork{}
	}
	var unit *sourcePkg
	if e.srcPkgSet != nil {
		unit = e.srcPkgSet[fn.Pkg()]
	}
	work := &funcInstWork{mangled: mangled, decl: decl, env: env, targs: targs, unit: unit}
	e.funcInsts[mangled] = work
	e.funcInstQueue = append(e.funcInstQueue, work)
	e.monoLog = append(e.monoLog, monoLogEntry{monoLogFuncInst, mangled})
	return nil
}

// ---- instantiated TYPE declarations (G3) ----

// typeInstWork is one pending instantiated-type declaration: the concrete
// instance and the mangled TypeId it declares under. Emission produces
// the TypeDef (struct fields / defined target already substituted by
// go/types in the instance's Underlying) plus one stenciled method per
// declared method of the origin — the FULL method set, so interface
// satisfaction and promotion stay complete (the D2 wire contract).
type typeInstWork struct {
	key  string
	inst *types.Named
	// The DECLARING unit (multi-package W1.1), like funcInstWork.unit:
	// the TypeDef/method stencils emit under it. Nil = current package.
	unit *sourcePkg
}

// instTypeIdForWire is instTypeId plus the TypeDef enqueue: use it
// whenever the mangled name actually REACHES the wire (a value type, a
// receiver TypeId), so every mentioned TypeId gets a declaration.
// (renderTypeArg deliberately uses bare instTypeId: a type that occurs
// only inside another mangled key does not need its own TypeDef.)
func (e *emitter) instTypeIdForWire(inst *types.Named) (string, error) {
	key, err := e.instTypeId(inst)
	if err != nil {
		return "", err
	}
	if err := e.enqueueTypeInst(inst, key); err != nil {
		return "", err
	}
	return key, nil
}

func (e *emitter) enqueueTypeInst(inst *types.Named, key string) error {
	obj := inst.Obj()
	// SOURCE-package generic types stencil (their declaration AST is
	// loaded — multi-package W1.1); stdlib generic types keep the
	// standing refusal (no AST to stencil from).
	if obj.Pkg() == nil || !e.isSourcePackage(obj.Pkg()) {
		// FR-23 (2026-09-04): a VALUE of an imported generic instantiation
		// never lowers (this refusal); in a declaration SIGNATURE the type
		// is carried as an opaque marker instead (wire.go sigOpaque), so
		// the enclosing declaration becomes a per-declaration stub and the
		// export survives — the census's whole-export kill is gone, the
		// members themselves stay refused by name.
		site := e.curFuncName
		if site == "" {
			site = "a package-level declaration"
		}
		return unsup("instantiation of imported generic type %s in %s (FR-23: no source to stencil an imported generic from — a value of this type never lowers; in a declaration signature it is an opaque marker and the declaration a fail-closed stub)", key, site)
	}
	var unit *sourcePkg
	if e.srcPkgSet != nil {
		unit = e.srcPkgSet[obj.Pkg()]
	}
	// Instantiated INTERFACES get no TypeDef stencil here: their
	// declaration (the satisfaction requirement list, with go/types'
	// already-substituted method set) comes from the seenInterfaces pass,
	// and a second entry under the same key would trip the duplicate-
	// TypeId refusal (caught by generics/generic-interface-value).
	if iface, isIface := inst.Underlying().(*types.Interface); isIface {
		if !iface.IsMethodSet() {
			return unsup("constraint interface %s used as a value type", key)
		}
		e.noteInterface(key, iface)
		return nil
	}
	if e.typeInsts == nil {
		e.typeInsts = map[string]*typeInstWork{}
	}
	if _, done := e.typeInsts[key]; done {
		return nil
	}
	work := &typeInstWork{key: key, inst: inst, unit: unit}
	e.typeInsts[key] = work
	e.typeInstQueue = append(e.typeInstQueue, work)
	e.monoLog = append(e.monoLog, monoLogEntry{monoLogTypeInst, key})
	return nil
}

// flushTypeInsts drains the instantiated-type queue, appending TypeDefs,
// stenciled methods, and their lifted literals. A method STENCIL — a
// method of a generic type at one receiver instantiation — whose body
// does not lower quarantines PER DECLARATION (FR-4, 2026-09-04, lane
// fr4-rowm; the H-3 residual closed): it becomes a signature-carrying
// stub under the instantiation's key (quarantinedStencilStub), the rest
// of the export lowers, and a CALL of it refuses by name. The stencil's
// own registrations (lifted literals, local types, mono journal incl.
// importedNamed) rolled back inside emitFuncInst; the stub's SIGNATURE
// then re-registers exactly the instantiations it mentions (emitted in
// SIGNATURE-OPAQUE mode, so an imported generic result type — FR-23 —
// composes as an opaque marker). A stencil whose signature does not lower
// even so still refuses the whole export (quarantinedMethodStub's
// sigRefusal: an incomplete method set is worse than a visible red).
// History: docs/bugfix-arc-log.md §H-3 (the residual), ledger FR-4.
func (e *emitter) flushTypeInsts(typeDefs, methods, funcs []any) ([]any, []any, []any, bool, error) {
	did := false
	for len(e.typeInstQueue) > 0 {
		work := e.typeInstQueue[0]
		e.typeInstQueue = e.typeInstQueue[1:]
		did = true
		// Stencil under the DECLARING unit (multi-package W1.1): the
		// method declarations' AST nodes key into that unit's Info.
		savedPkg, savedInfo := e.pkg, e.info
		if work.unit != nil {
			e.setUnit(work.unit)
		}
		underlying := work.inst.Underlying()
		if st, isStruct := underlying.(*types.Struct); isStruct {
			fields := []any{}
			for i := 0; i < st.NumFields(); i++ {
				fld := st.Field(i)
				fty, err := e.emitType(fld.Type())
				if err != nil {
					return nil, nil, nil, did, err
				}
				fields = append(fields, map[string]any{
					"name": fld.Name(), "type": fty, "embedded": fld.Anonymous()})
			}
			typeDefs = append(typeDefs, map[string]any{
				"name": work.key,
				"def":  map[string]any{"kind": "struct", "fields": fields},
			})
			// Promotion-wrapper candidate, like any declared struct type.
			e.namedStructTypes = append(e.namedStructTypes, work.inst)
		} else {
			target, err := e.emitType(underlying)
			if err != nil {
				return nil, nil, nil, did, err
			}
			typeDefs = append(typeDefs, map[string]any{
				"name": work.key,
				"def":  map[string]any{"kind": "defined", "target": target},
			})
		}
		for _, d := range e.genericMethodDecls[work.inst.Origin()] {
			m, err := e.emitMethodInst(work, d)
			if err != nil {
				// Per-declaration quarantine for METHOD STENCILS (FR-4):
				// an UNSUPPORTED stencil becomes a fail-closed stub
				// naming the instantiation and the inner cause; the
				// export survives. Non-unsupported errors (internal
				// invariants) still fail the export.
				var u unsupported
				if !errors.As(err, &u) {
					return nil, nil, nil, did, err
				}
				stub, serr := e.quarantinedStencilStub(work, d, u)
				if serr != nil {
					return nil, nil, nil, did, serr
				}
				methods = append(methods, stub)
				continue
			}
			funcs = append(funcs, e.lifted...)
			e.lifted = nil
			methods = append(methods, m)
		}
		e.pkg, e.info = savedPkg, savedInfo
	}
	return typeDefs, methods, funcs, did, nil
}

// quarantinedStencilStub builds the declaration-only stub for a method
// STENCIL whose body did not lower (FR-4): quarantinedMethodStub's shape
// (emit.go — `name`, `recvType`, `recv`, `params`, `results`, `variadic`,
// `unsupported`), built under the stencil's SUBSTITUTION so the receiver
// TypeId is the instantiation's mangled key and every parameter/result
// type is the instantiated one — the signature interface satisfaction
// reads (H-3's method-set-completeness invariant, now at one receiver
// instantiation). The refusal text names the instantiation
// (`main.box[int].render`) and carries the inner cause, so a call that
// lands on the stub says exactly which stencil refused and why.
//
// emitFuncInst has already restored the emitter state and rolled back
// the refused body's registrations; the substitution is re-entered here
// only for the signature. A substitution failure surfacing as an Invalid
// type (substErr) is re-raised — never a stub with a guessed signature.
func (e *emitter) quarantinedStencilStub(work *typeInstWork, d *ast.FuncDecl, u unsupported) (map[string]any, error) {
	env, targs, err := e.stencilEnv(work, d)
	if err != nil {
		return nil, err
	}
	savedSubst, savedName, savedErr, savedTargs := e.curSubst, e.curFuncName, e.substErr, e.curTargs
	e.curSubst, e.curFuncName, e.substErr, e.curTargs = env, work.key+"."+d.Name.Name, nil, targs
	defer func() {
		e.curSubst, e.curFuncName, e.substErr, e.curTargs = savedSubst, savedName, savedErr, savedTargs
	}()
	named := unsupported{what: "FR-4: method stencil at this instantiation does not lower — " + u.what}
	stub, err := e.quarantinedMethodStub(d, named)
	if err == nil && e.substErr != nil {
		err = e.substErr
	}
	if err != nil {
		return nil, err
	}
	return stub, nil
}

// stencilEnv binds a generic method declaration's RECEIVER type parameters
// (the only kind Go has — methods cannot add their own, spec §Method
// declarations) to the instantiation's arguments, in declaration order.
// Shared by emitMethodInst (the body) and quarantinedStencilStub (the
// signature of a refused body) so the two cannot substitute differently.
func (e *emitter) stencilEnv(work *typeInstWork, d *ast.FuncDecl) (map[*types.TypeParam]types.Type, []types.Type, error) {
	fn, ok := e.info.Defs[d.Name].(*types.Func)
	if !ok {
		return nil, nil, unsup("generic method %s has no definition object", d.Name.Name)
	}
	sig := fn.Type().(*types.Signature)
	rtp := sig.RecvTypeParams()
	targs := work.inst.TypeArgs()
	if rtp.Len() != targs.Len() {
		return nil, nil, unsup("receiver arity mismatch stenciling %s.%s: %d receiver params, %d args",
			work.key, d.Name.Name, rtp.Len(), targs.Len())
	}
	env := map[*types.TypeParam]types.Type{}
	targsList := make([]types.Type, targs.Len())
	for i := 0; i < rtp.Len(); i++ {
		env[rtp.At(i)] = targs.At(i)
		targsList[i] = targs.At(i)
	}
	return env, targsList, nil
}

// emitMethodInst stencils one method declaration at a receiver
// instantiation: the environment binds the method's RECEIVER type
// parameters (the only kind Go has — methods cannot add their own, spec
// §Method declarations) to the instance's arguments; the FuncId is
// receiverTypeId + "." + name, produced by the ordinary emitFuncDecl
// receiver path through the substitution-aware namedTypeName.
func (e *emitter) emitMethodInst(work *typeInstWork, d *ast.FuncDecl) (map[string]any, error) {
	env, targsList, err := e.stencilEnv(work, d)
	if err != nil {
		return nil, err
	}
	return e.emitFuncInst(&funcInstWork{
		mangled: work.key + "." + d.Name.Name, decl: d, env: env,
		targs: targsList, unit: work.unit})
}

// recordGenericMethod indexes a generic-receiver method declaration by
// its receiver's origin type, for per-instantiation stenciling.
func (e *emitter) recordGenericMethod(d *ast.FuncDecl) {
	fn, ok := e.info.Defs[d.Name].(*types.Func)
	if !ok {
		return
	}
	recv := fn.Type().(*types.Signature).Recv().Type()
	if ptr, isPtr := recv.(*types.Pointer); isPtr {
		recv = ptr.Elem()
	}
	named, ok := recv.(*types.Named)
	if !ok {
		return
	}
	if e.genericMethodDecls == nil {
		e.genericMethodDecls = map[*types.Named][]*ast.FuncDecl{}
	}
	origin := named.Origin()
	e.genericMethodDecls[origin] = append(e.genericMethodDecls[origin], d)
}

// genericFuncObj reports the generic *types.Func a use-site identifier
// denotes, or nil.
func (e *emitter) genericFuncObj(id *ast.Ident) *types.Func {
	fn, ok := e.info.Uses[id].(*types.Func)
	if !ok {
		return nil
	}
	sig, ok := fn.Type().(*types.Signature)
	if !ok || sig.TypeParams().Len() == 0 {
		return nil
	}
	return fn
}

// flushFuncInsts drains the stencil worklist (stencils can enqueue more —
// derived instantiations; the registry cap bounds the loop via
// registerMangledKey). An UNSUPPORTED stencil becomes a fail-closed stub
// exactly like a quarantined plain declaration: it refuses when CALLED,
// so one unsupported instantiation does not poison unrelated subjects in
// the same package. Non-unsupported errors fail the export.
func (e *emitter) flushFuncInsts(funcs []any) ([]any, error) {
	for len(e.funcInstQueue) > 0 {
		work := e.funcInstQueue[0]
		e.funcInstQueue = e.funcInstQueue[1:]
		fn, err := e.emitFuncInst(work)
		if err != nil {
			var u unsupported
			if errors.As(err, &u) {
				arity := 0
				if work.decl.Type.Params != nil {
					for _, f := range work.decl.Type.Params.List {
						n := len(f.Names)
						if n == 0 {
							n = 1
						}
						arity += n
					}
				}
				funcs = append(funcs, map[string]any{
					"name": work.mangled, "unsupported": u.what, "arity": arity})
				continue
			}
			return nil, err
		}
		funcs = append(funcs, e.lifted...)
		e.lifted = nil
		funcs = append(funcs, fn)
	}
	return funcs, nil
}

// emitFuncInst emits one stencil: the generic declaration's body under the
// work item's substitution, named by the mangled FuncId. Lifted literals
// inherit the mangled name (curFuncName), so `outer[int]$lit0` and
// `outer[string]$lit0` stay distinct program-wide. On failure every
// half-registered artifact of the stencil (lifted literals, local type
// defs, wrapper candidates) rolls back, exactly like the per-decl
// quarantine in emitProgram.
func (e *emitter) emitFuncInst(work *funcInstWork) (map[string]any, error) {
	savedSubst, savedName, savedErr := e.curSubst, e.curFuncName, e.substErr
	savedTargs := e.curTargs
	// Stencil bodies emit under their DECLARING unit's type-checker
	// record (multi-package W1.1): the body's AST nodes are keyed there.
	savedPkg, savedInfo := e.pkg, e.info
	if work.unit != nil {
		e.setUnit(work.unit)
	}
	e.curSubst, e.curFuncName, e.substErr = work.env, work.mangled, nil
	e.curTargs = work.targs
	e.liftSeq = 0
	liftedMark := len(e.lifted)
	localTypesMark := len(e.localTypeDefs)
	localIfaceMark := len(e.localIfaceMethods)
	namedStructMark := len(e.namedStructTypes)
	// BUG-031: the $deferRecoverNoop registration rides e.lifted and must
	// roll back with it.
	deferNoopMark := e.deferNoopEmitted
	monoMark := e.markMono()
	fn, err := e.emitFuncDecl(work.decl)
	if err == nil && e.substErr != nil {
		// A substitution failure that surfaced as an Invalid type but was
		// swallowed by an emission path: refuse anyway (fail closed).
		err = e.substErr
	}
	e.curSubst, e.curFuncName, e.substErr = savedSubst, savedName, savedErr
	e.curTargs = savedTargs
	e.pkg, e.info = savedPkg, savedInfo
	if err != nil {
		e.lifted = e.lifted[:liftedMark]
		e.deferNoopEmitted = deferNoopMark
		e.localTypeDefs = e.localTypeDefs[:localTypesMark]
		e.localIfaceMethods = e.localIfaceMethods[:localIfaceMark]
		e.namedStructTypes = e.namedStructTypes[:namedStructMark]
		e.rollbackMono(monoMark)
		return nil, err
	}
	// Plain functions are keyed by the mangled FuncId directly; METHOD
	// stencils keep their declared name — their wire key is
	// recvType + "." + name, and recvType is already the mangled receiver
	// TypeId (namedTypeName under the active substitution).
	if work.decl.Recv == nil {
		fn["name"] = work.mangled
	}
	return fn, nil
}

// drainMono drains BOTH instantiation queues to a joint fixpoint:
// function stencils can reach new instantiated types, and type stencils
// (fields, methods) can reach new function instantiations. Termination:
// every registration passes the capped mangled-key registry.
func (e *emitter) drainMono(funcs, typeDefs, methods []any) ([]any, []any, []any, error) {
	for {
		var err error
		funcs, err = e.flushFuncInsts(funcs)
		if err != nil {
			return nil, nil, nil, err
		}
		var did bool
		typeDefs, methods, funcs, did, err = e.flushTypeInsts(typeDefs, methods, funcs)
		if err != nil {
			return nil, nil, nil, err
		}
		if !did && len(e.funcInstQueue) == 0 {
			return funcs, typeDefs, methods, nil
		}
	}
}

// monoRegistryCap bounds the number of distinct mangled keys (decision
// §9.4): go/types' mono check guarantees the instantiation closure is
// FINITE for every program our conf.Check accepts, but not small — a
// multiplicative instantiation chain stays finite while growing beyond any
// constant. Exceeding the cap fails the export loudly; never silent
// truncation.
const monoRegistryCap = 10000

// ---- quarantine rollback (audit response m5) ----
//
// Every mono registration (mangled key, function stencil, type stencil)
// is journaled so the per-decl quarantine can UNDO registrations made by
// a declaration that is then refused: without this, a quarantined body's
// instantiations survived into the worklists, and one unsupported TYPE
// stencil (which has no quarantine) killed the whole export — poisoning
// subjects the refused declaration never touched (pinned by
// generics/quarantined-instantiation).

type monoLogKind int

const (
	monoLogMangled monoLogKind = iota
	monoLogFuncInst
	monoLogTypeInst
	// Delta-review R1: interfaces and dispatch targets recorded by a
	// refused body must roll back too — the seenInterfaces declaration
	// pass and the anchor synthesis FAIL THE WHOLE EXPORT on an
	// unsupported signature, so a surviving registration poisons subjects
	// the refused declaration never touched (the etcd-raft
	// `Ready() <-chan Ready` shape).
	monoLogSeenIface
	monoLogCalledIface
	// FR-24's neighbour (2026-09-04, lane fr24): an IMPORTED named type
	// recorded by a refused body (`reflect.Value` from binary.Write's
	// reflect slow path; any user body touching reflect) must roll back
	// too — the D5 method-set stub pass (importedTypeDecls) needs EVERY
	// signature of the type to lower and skips whole when one does not
	// (`Complex() complex128`), and the interfaces its signatures noted
	// on the way (`reflect.Type`, with `OverflowComplex(complex128)`)
	// then FAIL THE WHOLE EXPORT in the interface declaration pass. The
	// dry-run pre-pass's comment used to list importedNamed as a known,
	// harmless rollback gap ("never a changed answer"): refuted — the
	// answer changed from one stub to a whole-export kill, and it masked
	// itself behind FR-24's structSize kill on cedar-go.
	monoLogImportedNamed
)

type monoLogEntry struct {
	kind monoLogKind
	key  string
}

// monoMarks snapshots the journal, both queues and the interface
// conflict list; take one BEFORE emitting a quarantinable body.
type monoMarks struct {
	log, funcQ, typeQ int
	// len(e.ifaceConflicts) at the mark (audit fix R3, 2026-09-05): a
	// conflict recorded by a body that is later per-decl quarantined
	// belongs to the discarded body and must not refuse the export.
	// Truncation, not key deletion: the list is append-only between
	// emissions and may hold duplicates of one pair (the emitProgram
	// check dedups), so deleting by key could drop a pre-mark record.
	ifaceConf int
}

func (e *emitter) markMono() monoMarks {
	return monoMarks{log: len(e.monoLog), funcQ: len(e.funcInstQueue), typeQ: len(e.typeInstQueue),
		ifaceConf: len(e.ifaceConflicts)}
}

// rollbackMono undoes every registration journaled after the marks.
// Queue truncation to the recorded lengths is exact: pops happen only
// between emissions (flushFuncInsts), never inside one, so entries past
// the mark are exactly this emission's appends. The same holds for
// ifaceConflicts (noteInterface only ever appends).
func (e *emitter) rollbackMono(m monoMarks) {
	for _, entry := range e.monoLog[m.log:] {
		switch entry.kind {
		case monoLogMangled:
			delete(e.mangledKeys, entry.key)
		case monoLogFuncInst:
			delete(e.funcInsts, entry.key)
		case monoLogTypeInst:
			delete(e.typeInsts, entry.key)
		case monoLogSeenIface:
			delete(e.seenInterfaces, entry.key)
		case monoLogCalledIface:
			delete(e.calledIfaceMethods, entry.key)
		case monoLogImportedNamed:
			delete(e.importedNamed, entry.key)
		}
	}
	e.monoLog = e.monoLog[:m.log]
	e.funcInstQueue = e.funcInstQueue[:m.funcQ]
	e.typeInstQueue = e.typeInstQueue[:m.typeQ]
	e.ifaceConflicts = e.ifaceConflicts[:m.ifaceConf]
}

// registerMangledKey records key → t in the collision registry. Two
// NON-Identical types under one key would let GoCore decide two distinct
// Go types identical — refuse the export (belt and suspenders behind the
// §3.2 injectivity argument: `[` cannot occur in a Go identifier, and the
// package-name collision gate covers the qualifier space). Identical types
// under one key are fine (e.g. byte- and uint8-instantiations share a key
// because they ARE one Go type).
func (e *emitter) registerMangledKey(key string, t types.Type) error {
	if e.mangledKeys == nil {
		e.mangledKeys = map[string]types.Type{}
	}
	if prev, ok := e.mangledKeys[key]; ok {
		if !types.Identical(prev, t) {
			return unsup("mangled TypeId collision: %q names both %s and %s", key, prev, t)
		}
		return nil
	}
	if len(e.mangledKeys) >= monoRegistryCap {
		return unsup("instantiation registry exceeded %d distinct mangled keys (monomorphization cap, design note §2e)", monoRegistryCap)
	}
	e.mangledKeys[key] = t
	e.monoLog = append(e.monoLog, monoLogEntry{monoLogMangled, key})
	return nil
}

// instTypeId returns the wire TypeId key for an INSTANTIATED named type
// (fully concrete type arguments only — substitution happens before the
// mangler is consulted), registering it in the collision registry.
func (e *emitter) instTypeId(inst *types.Named) (string, error) {
	if inst.TypeArgs().Len() == 0 {
		return "", unsup("instTypeId on non-instantiated named type %s", inst)
	}
	args, err := e.renderTypeArgList(inst.TypeArgs())
	if err != nil {
		return "", err
	}
	key := e.qualifiedTypeName(inst.Obj()) + "[" + args + "]"
	if err := e.registerMangledKey(key, inst); err != nil {
		return "", err
	}
	return key, nil
}

// instFuncId returns the wire FuncId for an instantiated generic FUNCTION:
// the bare declared name (plain function FuncIds are unqualified on the
// wire) plus the bracketed argument list. Instantiated METHOD FuncIds are
// receiverTypeId + "." + methodName, where the receiver TypeId comes from
// instTypeId — no separate constructor.
func (e *emitter) instFuncId(name string, targs []types.Type) (string, error) {
	rendered := make([]string, len(targs))
	for i, t := range targs {
		r, err := e.renderTypeArg(t)
		if err != nil {
			return "", err
		}
		rendered[i] = r
	}
	return name + "[" + strings.Join(rendered, ",") + "]", nil
}

func (e *emitter) renderTypeArgList(list *types.TypeList) (string, error) {
	parts := make([]string, list.Len())
	for i := 0; i < list.Len(); i++ {
		r, err := e.renderTypeArg(list.At(i))
		if err != nil {
			return "", err
		}
		parts[i] = r
	}
	return strings.Join(parts, ","), nil
}

// renderTypeArg renders one type argument in the runtime's spelling (see
// the file comment). Types outside the admitted mangling surface
// (channels, anonymous non-empty structs/interfaces, unsubstituted type
// parameters) fail closed, keeping the key space inside the injectivity
// argument. RATIONALE CORRECTED (arc-final audit F9, 2026-08-08): this
// comment used to also claim "none of them can reach a supported wire
// type either" — true when written (pre-channels), FALSE since the
// channels arc made chan a first-class wire type (emitType's
// *types.Chan case, wire.go). The refusal for channels is now a pure
// COVERAGE gap, not a wire impossibility: any generic instantiation
// whose type argument structurally contains an UNNAMED channel type
// (chan int, []chan int, map[k]chan int, ...) is refused even when the
// generic performs no channel operation, while the NAMED spelling
// (type C chan int) reaches the Named arm and works — the split the
// corpus pin generics/chan-type-arg records red (the one existing
// guardrail, type-parameter-channel-ops, instantiates at a named type
// and so never saw this). A future *types.Chan arm needs a mangled
// spelling with direction+elem inside the injectivity argument.
// TestManglingSurfaceFailsClosed pins the refusal itself.
func (e *emitter) renderTypeArg(t types.Type) (string, error) {
	switch ty := t.(type) {
	case *types.Basic:
		return renderBasicArg(ty)
	case *types.Named:
		// FUNCTION-LOCAL defined types refuse (audit response M3, a
		// recorded narrowing): gc names them in instantiation renderings
		// with a compiler-internal, globally-unique suffix (probe
		// 2026-08-05: two same-named locals render `main.score·1` /
		// `main.score·2`), which a bare `pkg.Name` key can neither
		// reproduce (observation/panic-text divergence) nor keep
		// injective (two same-named locals in different functions would
		// share one key — the collision registry catches the two-type
		// case loud, mono_test pins it, but the single-type divergence is
		// silent). Refusing beats shipping a guessed numbering.
		if obj := ty.Obj(); obj.Pkg() != nil && obj.Parent() != obj.Pkg().Scope() {
			return "", unsup("function-local defined type %s as a type argument (gc renders these with a compiler-internal unique suffix, e.g. %s·1 — refused rather than guessed)",
				obj.Name(), obj.Name())
		}
		if ty.TypeArgs().Len() > 0 {
			return e.instTypeId(ty)
		}
		return e.qualifiedTypeName(ty.Obj()), nil
	case *types.Alias:
		// Aliases are transparent for identity (§3.2): render the aliased
		// type; aliases never mint TypeIds.
		return e.renderTypeArg(types.Unalias(ty))
	case *types.Pointer:
		elem, err := e.renderTypeArg(ty.Elem())
		if err != nil {
			return "", err
		}
		return "*" + elem, nil
	case *types.Slice:
		elem, err := e.renderTypeArg(ty.Elem())
		if err != nil {
			return "", err
		}
		return "[]" + elem, nil
	case *types.Array:
		elem, err := e.renderTypeArg(ty.Elem())
		if err != nil {
			return "", err
		}
		return "[" + itoa64(ty.Len()) + "]" + elem, nil
	case *types.Map:
		key, err := e.renderTypeArg(ty.Key())
		if err != nil {
			return "", err
		}
		val, err := e.renderTypeArg(ty.Elem())
		if err != nil {
			return "", err
		}
		return "map[" + key + "]" + val, nil
	case *types.Signature:
		return e.renderSignatureArg(ty)
	case *types.Interface:
		if ty.Empty() {
			// reflect's spelling of the empty interface (G1 probe:
			// Vec[any] names as "Vec[interface {}]").
			return "interface {}", nil
		}
		return "", unsup("anonymous non-empty interface as a type argument (%s)", ty)
	case *types.Struct:
		if ty.NumFields() == 0 {
			// The canonical EMPTY struct is inside the admitted type
			// surface (the map[K]struct{} set idiom) and reflect spells
			// it "struct {}" in instantiation names (audit response m4,
			// probe 2026-08-05: Bx[struct{}] names as "Bx[struct {}]").
			// The first cut's default arm over-refused it.
			return "struct {}", nil
		}
		return "", unsup("anonymous non-empty struct as a type argument (%s)", ty)
	case *types.TypeParam:
		return "", unsup("unsubstituted type parameter %s as a type argument", ty)
	default:
		return "", unsup("type argument outside the mangling surface: %T (%s)", t, t)
	}
}

// renderSignatureArg matches reflect's func-type spelling: parameters
// ", "-joined, variadic "...T", results "" / " T" / " (T, U)" (G1 probe:
// "func(int, string) (int, error)", "func(...int) int").
func (e *emitter) renderSignatureArg(sig *types.Signature) (string, error) {
	params := make([]string, sig.Params().Len())
	for i := 0; i < sig.Params().Len(); i++ {
		p, err := e.renderTypeArg(sig.Params().At(i).Type())
		if err != nil {
			return "", err
		}
		if sig.Variadic() && i == sig.Params().Len()-1 {
			p = "..." + strings.TrimPrefix(p, "[]")
		}
		params[i] = p
	}
	out := "func(" + strings.Join(params, ", ") + ")"
	switch sig.Results().Len() {
	case 0:
		return out, nil
	case 1:
		r, err := e.renderTypeArg(sig.Results().At(0).Type())
		if err != nil {
			return "", err
		}
		return out + " " + r, nil
	default:
		results := make([]string, sig.Results().Len())
		for i := 0; i < sig.Results().Len(); i++ {
			r, err := e.renderTypeArg(sig.Results().At(i).Type())
			if err != nil {
				return "", err
			}
			results[i] = r
		}
		return out + " (" + strings.Join(results, ", ") + ")", nil
	}
}

// renderBasicArg spells basic kinds the way the runtime does: reflect
// names byte as uint8 and rune as int32 (G1 probe), so the canonical name
// comes from the KIND, never Basic.Name() (go/types' universe byte/rune
// are distinct *Basic values with the alias name).
func renderBasicArg(b *types.Basic) (string, error) {
	switch b.Kind() {
	case types.Bool:
		return "bool", nil
	case types.Int:
		return "int", nil
	case types.Int8:
		return "int8", nil
	case types.Int16:
		return "int16", nil
	case types.Int32:
		return "int32", nil
	case types.Int64:
		return "int64", nil
	case types.Uint:
		return "uint", nil
	case types.Uint8:
		return "uint8", nil
	case types.Uint16:
		return "uint16", nil
	case types.Uint32:
		return "uint32", nil
	case types.Uint64:
		return "uint64", nil
	case types.Uintptr:
		return "uintptr", nil
	case types.Float32:
		return "float32", nil
	case types.Float64:
		return "float64", nil
	case types.Complex64:
		return "complex64", nil
	case types.Complex128:
		return "complex128", nil
	case types.String:
		return "string", nil
	default:
		return "", unsup("basic type %s as a type argument", b)
	}
}

func itoa64(n int64) string {
	if n < 0 {
		// Array lengths are non-negative; refuse loudly via a spelling that
		// cannot collide with a legal rendering.
		return "-" + itoa(int(-n))
	}
	return itoa(int(n))
}
