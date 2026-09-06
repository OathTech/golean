package main

// Exact positive metadata travels with the entry that produced it. The private
// payload is a Go struct, not a wire object: existing recursive wire checks do
// not mistake a positive type for an executable type. sealDeclarations moves
// it into the separate envelope and copies the executable entry without it.

import (
	"go/types"
	"sort"
)

const declarationEntryKey = "$declaration"

type declarationEntry struct {
	facts    map[string]any
	nominals map[string]int
	err      error
}

// Positive identity emission may record displays, local ordinals and key
// hazards. Isolate that bookkeeping from executable emission, including when
// a declaration's body is subsequently rolled back. Shared source/type-checker
// records are read-only; the clone owns every identity map it can write.
func (e *emitter) declarationScope() *emitter {
	d := *e
	d.typeDisplays = nil
	d.displayConflicts = nil
	d.badKeyPaths = nil
	d.localOrdinals = nil
	d.badLocalTypes = nil
	d.mangledKeys = nil
	d.substErr = nil
	d.declarationNominals = map[string]int{}
	return &d
}

func declarationSignature(params, results []types.Type, variadic bool) *types.Signature {
	tuple := func(ts []types.Type) *types.Tuple {
		vs := make([]*types.Var, len(ts))
		for i, t := range ts {
			vs[i] = types.NewVar(0, nil, "", t)
		}
		return types.NewTuple(vs...)
	}
	return types.NewSignatureType(nil, nil, nil, tuple(params), tuple(results), variadic)
}

func declarationTupleTypes(ts *types.Tuple) []types.Type {
	out := make([]types.Type, ts.Len())
	for i := range out {
		out[i] = ts.At(i).Type()
	}
	return out
}

// A source stencil can have phantom type parameters absent from its signature.
// Check every parameter's actual substitution before forming its closed source
// signature, rather than treating the uninstantiated declaration as closed.
func (e *emitter) closedDeclarationSignature(sig *types.Signature) (map[string]any, error) {
	if sig == nil {
		return nil, unsup("declaration has no source signature")
	}
	for i := 0; i < sig.TypeParams().Len(); i++ {
		if _, ok := e.curSubst[sig.TypeParams().At(i)]; !ok {
			return nil, unsup("declaration signature has unbound type parameter %s", sig.TypeParams().At(i))
		}
	}
	return e.emitDeclarationSignature(declarationSignature(
		declarationTupleTypes(sig.Params()), declarationTupleTypes(sig.Results()), sig.Variadic()))
}

func (e *emitter) declarationRecord(build func(*emitter) (map[string]any, error)) *declarationEntry {
	d := e.declarationScope()
	facts, err := build(d)
	if err == nil {
		err = d.checkKeyPathGrammar()
	}
	if err == nil {
		err = d.checkLocalTypeOrdinals()
	}
	if err == nil {
		err = d.substErr
	}
	return &declarationEntry{facts: facts, nominals: d.declarationNominals, err: err}
}

func (e *emitter) sourceDeclaration(sig *types.Signature) *declarationEntry {
	return e.declarationRecord(func(d *emitter) (map[string]any, error) {
		s, err := d.closedDeclarationSignature(sig)
		return map[string]any{"kind": "source", "signature": s, "sourceSignature": s}, err
	})
}

func (e *emitter) closureDeclaration(sig *types.Signature, captures []*types.Var) *declarationEntry {
	return e.declarationRecord(func(d *emitter) (map[string]any, error) {
		source, err := d.closedDeclarationSignature(sig)
		if err != nil {
			return nil, err
		}
		prefix := make([]any, len(captures))
		params := make([]types.Type, 0, len(captures)+sig.Params().Len())
		for i, v := range captures {
			t := types.NewPointer(v.Type())
			prefix[i], err = d.emitDeclarationType(t)
			if err != nil {
				return nil, err
			}
			params = append(params, t)
		}
		params = append(params, declarationTupleTypes(sig.Params())...)
		abi, err := d.emitDeclarationSignature(declarationSignature(params,
			declarationTupleTypes(sig.Results()), sig.Variadic()))
		return map[string]any{"kind": "closure", "signature": abi,
			"sourceSignature": source, "captures": prefix}, err
	})
}

func (e *emitter) helperDeclaration(role string, params, results []types.Type) *declarationEntry {
	return e.declarationRecord(func(d *emitter) (map[string]any, error) {
		sig, err := d.emitDeclarationSignature(declarationSignature(params, results, false))
		return map[string]any{"kind": "synthetic", "helper": role, "signature": sig}, err
	})
}

func declarationReceiver(named *types.Named, pointer bool) types.Type {
	if pointer {
		return types.NewPointer(named)
	}
	return named
}

func (e *emitter) methodDeclaration(role string, method *types.Func, receiver types.Type) *declarationEntry {
	return e.declarationRecord(func(d *emitter) (map[string]any, error) {
		if method == nil || receiver == nil {
			return nil, unsup("method declaration has no Go method or adapter receiver")
		}
		sig, ok := method.Type().(*types.Signature)
		if !ok || sig.Recv() == nil {
			return nil, unsup("method declaration %s has no receiver signature", method.Name())
		}
		s, err := d.closedDeclarationSignature(sig)
		if err != nil {
			return nil, err
		}
		r, err := d.emitDeclarationType(receiver)
		if err != nil {
			return nil, err
		}
		original, err := d.emitDeclarationType(sig.Recv().Type())
		return map[string]any{"kind": role, "member": declarationObjectName(method),
			"receiver": r, "sourceReceiver": original, "signature": s}, err
	})
}

func (e *emitter) funcDeclaration(d *types.Func) *declarationEntry {
	if d == nil {
		return &declarationEntry{err: unsup("function declaration has no Go definition")}
	}
	sig, ok := d.Type().(*types.Signature)
	if !ok {
		return &declarationEntry{err: unsup("function declaration %s has no signature", d.Name())}
	}
	if sig.Recv() != nil {
		return e.methodDeclaration("source", d, sig.Recv().Type())
	}
	return e.sourceDeclaration(sig)
}

func (e *emitter) stencilFunctionDeclaration(work *funcInstWork) *declarationEntry {
	d := e.declarationScope()
	if work.unit != nil {
		d.setUnit(work.unit)
	}
	d.curSubst, d.curTargs, d.curInstDecl = work.env, work.targs, work.decl
	obj, _ := d.info.Defs[work.decl.Name].(*types.Func)
	return d.funcDeclaration(obj)
}

func (e *emitter) syncHelperDeclaration(role, primitive string, extra []types.Type) *declarationEntry {
	named := e.syncUsed[primitive]
	if named == nil {
		return &declarationEntry{err: unsup("synthetic %s has no Go sync.%s declaration", role, primitive)}
	}
	return e.helperDeclaration(role, append([]types.Type{types.NewPointer(named)}, extra...), nil)
}

func cloneDeclarationObject(o map[string]any) map[string]any {
	out := make(map[string]any, len(o))
	for k, v := range o {
		if k != declarationEntryKey {
			out[k] = v
		}
	}
	return out
}

// The final arrays determine indices. Construction-point payloads follow their
// entries through renaming, ordering and quarantine rollback; no name lookup
// attempts to rediscover a declaration from an opaque runtime spelling.
func (e *emitter) sealDeclarations(program map[string]any) error {
	nominals := map[string]int{}
	merge := func(entry *declarationEntry) error {
		if entry.err != nil {
			return entry.err
		}
		for id, arity := range entry.nominals {
			if old, ok := nominals[id]; ok && old != arity {
				return unsup("package declaration origin %s has conflicting arities", id)
			}
			nominals[id] = arity
		}
		return nil
	}
	packages := make([]any, 0, len(e.units))
	sourceNominals := map[string]bool{}
	for _, unit := range e.units {
		packages = append(packages, unit.path)
		d := e.declarationScope()
		d.curSubst, d.curTargs, d.curInstDecl = nil, nil, nil
		for _, name := range unit.pkg.Scope().Names() {
			obj, ok := unit.pkg.Scope().Lookup(name).(*types.TypeName)
			if !ok || obj.IsAlias() {
				continue
			}
			named, ok := obj.Type().(*types.Named)
			if !ok {
				return unsup("package source declaration %s is not a defined type", name)
			}
			id := d.qualifiedTypeName(named.Origin().Obj())
			d.declarationNominals[id] = named.Origin().TypeParams().Len()
			sourceNominals[id] = true
		}
		if err := d.checkKeyPathGrammar(); err != nil {
			return err
		}
		if err := merge(&declarationEntry{nominals: d.declarationNominals}); err != nil {
			return err
		}
	}
	envelope := map[string]any{"schema": "golean-declarations-v1", "packages": packages}
	seen := map[string]bool{}
	for _, table := range []string{"funcs", "methods"} {
		values, ok := program[table].([]any)
		if !ok {
			return unsup("package declarations: missing %s table", table)
		}
		facts, clean := make([]any, len(values)), make([]any, len(values))
		for i, value := range values {
			m, ok := value.(map[string]any)
			if !ok {
				return unsup("package declarations: %s[%d] is not an object", table, i)
			}
			id, _ := m["name"].(string)
			if table == "methods" {
				recv, _ := m["recvType"].(string)
				if recv == "" {
					return unsup("package declarations: method %s has no receiver identity", id)
				}
				id = recv + "." + id
			}
			if id == "" || seen[id] {
				return unsup("package declarations: empty or duplicate function identity %q", id)
			}
			seen[id] = true
			entry, ok := m[declarationEntryKey].(*declarationEntry)
			if !ok || entry == nil {
				return unsup("package declarations: %s[%d] %s has no construction-point facts", table, i, id)
			}
			if err := merge(entry); err != nil {
				return unsup("package declarations: %s[%d] %s: %v", table, i, id, err)
			}
			f := cloneDeclarationObject(entry.facts)
			f["index"], f["id"] = i, id
			if table == "methods" {
				f["receiverId"] = m["recvType"]
			}
			facts[i], clean[i] = f, cloneDeclarationObject(m)
		}
		envelope[table], program[table] = facts, clean
	}
	interfaces := []any{}
	for i, value := range program["types"].([]any) {
		td := value.(map[string]any)
		def := td["def"].(map[string]any)
		if def["kind"] != "interface" {
			continue
		}
		name := td["name"].(string)
		iface := e.seenInterfaces[name]
		if iface == nil {
			return unsup("package declarations: interface %s has no complete Go requirement set", name)
		}
		entry := e.declarationRecord(func(d *emitter) (map[string]any, error) {
			ty, err := d.emitDeclarationType(iface)
			return map[string]any{"index": i, "id": name, "type": ty}, err
		})
		if err := merge(entry); err != nil {
			return unsup("package declarations: interface %s: %v", name, err)
		}
		interfaces = append(interfaces, entry.facts)
	}
	keys := make([]string, 0, len(nominals))
	for key := range nominals {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	ns := make([]any, len(keys))
	for i, key := range keys {
		ns[i] = map[string]any{"id": key, "arity": nominals[key]}
	}
	sourceKeys := make([]string, 0, len(sourceNominals))
	for key := range sourceNominals {
		sourceKeys = append(sourceKeys, key)
	}
	sort.Strings(sourceKeys)
	envelope["nominals"], envelope["sourceNominals"], envelope["interfaces"] = ns, sourceKeys, interfaces
	program["declarations"] = envelope
	return nil
}

// Shadow models are emitted by the same producer before their method harvest.
// Reattach the exact already-produced metadata to the harvested entries; do not
// reconstruct their source identities from lowered params or model layouts.
func restoreModelDeclarations(program map[string]any) error {
	env, ok := program["declarations"].(map[string]any)
	if !ok {
		return unsup("model harvest has no declaration envelope")
	}
	nominals := map[string]int{}
	for _, n := range env["nominals"].([]any) {
		m := n.(map[string]any)
		nominals[m["id"].(string)] = m["arity"].(int)
	}
	methods := program["methods"].([]any)
	facts := env["methods"].([]any)
	if len(methods) != len(facts) {
		return unsup("model declaration harvest has mismatched method inventory")
	}
	for i, m := range methods {
		entry := cloneDeclarationObject(facts[i].(map[string]any))
		entry["kind"] = "model"
		m.(map[string]any)[declarationEntryKey] = &declarationEntry{facts: entry, nominals: nominals}
	}
	return nil
}
