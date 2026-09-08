package main

// Positive declaration facts for I1. This serializer does not ask whether a
// type has an executable representation, register an opaque TypeDef, or inspect
// a function body. Its output is a separate schema; it is not accepted by the
// current executable-type decoder. Connecting it to package admission and the
// clean code table is a subsequent change.

import (
	"go/types"
	"maps"
	"slices"
	"sort"
)

// A declaration query borrows only checked source facts and the current
// substitution inputs. Identity helpers use this fresh emitter's registries;
// no executable-emitter map, diagnostic slice or instantiation cache is shared.
// Embedding reuses the existing identity/substitution algorithms without
// copying the executable emitter and its mutable output state.
type declarationEmitter struct{ emitter }

func (e *emitter) emitDeclarationType(t types.Type) (any, error) {
	d := &declarationEmitter{emitter: emitter{
		fset: e.fset, info: e.info, pkg: e.pkg,
		units:    slices.Clone(e.units),
		curSubst: maps.Clone(e.curSubst), curTargs: slices.Clone(e.curTargs),
		curInstDecl: e.curInstDecl, substErr: e.substErr,
	}}
	value, err := d.emitDeclarationType(t)
	if err != nil {
		return nil, err
	}
	// Isolation must not discard alarms raised while minting an identity,
	// including identities nested in a composite or active substitution.
	if err := d.checkKeyPathGrammar(); err != nil {
		return nil, err
	}
	if err := d.displayConflictRefusal(); err != nil {
		return nil, err
	}
	return value, nil
}

// A Go identifier's package participates in identity only when unexported.
// This is used for anonymous struct fields and interface methods, not for
// nominal type declarations, which always have their own TypeId.
func declarationObjectName(obj types.Object) (map[string]any, error) {
	pkg := ""
	if !obj.Exported() {
		if obj.Pkg() == nil || obj.Pkg().Path() == "" {
			return nil, unsup("declaration private member %s has no package identity", obj.Name())
		}
		pkg = obj.Pkg().Path()
	}
	return map[string]any{"name": obj.Name(), "package": pkg}, nil
}

func (e *declarationEmitter) emitDeclarationTuple(tuple *types.Tuple) ([]any, error) {
	values := make([]any, tuple.Len())
	for i := range values {
		ty, err := e.emitDeclarationType(tuple.At(i).Type())
		if err != nil {
			return nil, err
		}
		values[i] = ty
	}
	return values, nil
}

// Parameter names are binding facts of a definition, not function type
// identity. A receiver is likewise excluded from the function signature;
// method declarations carry its positive type as a separate fact.
func (e *declarationEmitter) emitDeclarationSignature(sig *types.Signature) (map[string]any, error) {
	if sig.TypeParams().Len() != 0 {
		return nil, unsup("declaration signature has uninstantiated type parameters")
	}
	params, err := e.emitDeclarationTuple(sig.Params())
	if err != nil {
		return nil, err
	}
	results, err := e.emitDeclarationTuple(sig.Results())
	if err != nil {
		return nil, err
	}
	return map[string]any{"kind": "func", "params": params, "results": results,
		"variadic": sig.Variadic()}, nil
}

func (e *declarationEmitter) emitDeclarationType(t types.Type) (any, error) {
	if e.curSubst != nil {
		t = e.applySubst(t)
	}
	switch ty := t.(type) {
	case *types.Alias:
		return e.emitDeclarationType(types.Unalias(ty))
	case *types.Basic:
		if ty.Kind() == types.Invalid && e.substErr != nil {
			return nil, e.substErr
		}
		// No defaulting of untyped constants: this channel describes declared
		// types. Complex and unsafe.Pointer are positive identities even when
		// an executable use would be refused by the separate support boundary.
		basics := map[types.BasicKind]string{
			types.Bool: "bool", types.String: "string",
			types.Int: "int", types.Int8: "int8", types.Int16: "int16",
			types.Int32: "int32", types.Int64: "int64",
			types.Uint: "uint", types.Uint8: "uint8", types.Uint16: "uint16",
			types.Uint32: "uint32", types.Uint64: "uint64", types.Uintptr: "uintptr",
			types.Float32: "float32", types.Float64: "float64",
			types.Complex64: "complex64", types.Complex128: "complex128",
			types.UnsafePointer: "unsafe.Pointer",
		}
		name, ok := basics[ty.Kind()]
		if !ok {
			return nil, unsup("invalid or untyped declaration basic %s", ty)
		}
		return map[string]any{"kind": "basic", "basic": name}, nil
	case *types.Named:
		if ty.TypeParams().Len() != ty.TypeArgs().Len() {
			return nil, unsup("declaration type %s has uninstantiated type parameters", ty)
		}
		// Naming a constraint does not make it a runtime interface type.
		// This includes the predeclared comparable and aliases to a named
		// constraint; ordinary named method-set interfaces remain positive.
		if iface, ok := ty.Underlying().(*types.Interface); ok && !iface.IsMethodSet() {
			return nil, unsup("declaration interface has non-method type-set terms")
		}
		args := make([]any, ty.TypeArgs().Len())
		for i := range args {
			arg, err := e.emitDeclarationType(ty.TypeArgs().At(i))
			if err != nil {
				return nil, err
			}
			args[i] = arg
		}
		// Keep the declaration identity and ordered instantiation arguments
		// separately. No display parsing and no invented named basic type.
		obj := ty.Origin().Obj()
		if obj.Pkg() == nil {
			if types.Universe.Lookup(obj.Name()) != obj {
				return nil, unsup("declaration nominal %s has no package identity", obj.Name())
			}
		} else if obj.Pkg().Path() == "" {
			return nil, unsup("declaration nominal %s has no package identity", obj.Name())
		}
		if pkg := obj.Pkg(); pkg != nil && obj.Parent() != pkg.Scope() {
			if _, ok := e.localTypeOrdinal(obj); !ok {
				return nil, unsup("declaration identity has no local type ordinal: %s", obj.Name())
			}
		}
		id := e.qualifiedTypeName(obj)
		if e.substErr != nil {
			return nil, e.substErr
		}
		return map[string]any{"kind": "named", "id": id,
			"args": args}, nil
	case *types.Pointer:
		elem, err := e.emitDeclarationType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "pointer", "elem": elem}, nil
	case *types.Slice:
		elem, err := e.emitDeclarationType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "slice", "elem": elem}, nil
	case *types.Array:
		if ty.Len() < 0 {
			return nil, unsup("declaration array has unknown length")
		}
		elem, err := e.emitDeclarationType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "array", "len": ty.Len(), "elem": elem}, nil
	case *types.Map:
		key, err := e.emitDeclarationType(ty.Key())
		if err != nil {
			return nil, err
		}
		elem, err := e.emitDeclarationType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "map", "key": key, "elem": elem}, nil
	case *types.Chan:
		var direction string
		switch ty.Dir() {
		case types.SendRecv:
			direction = "both"
		case types.SendOnly:
			direction = "send"
		case types.RecvOnly:
			direction = "recv"
		default:
			return nil, unsup("declaration channel has invalid direction %d", ty.Dir())
		}
		elem, err := e.emitDeclarationType(ty.Elem())
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "chan", "direction": direction, "elem": elem}, nil
	case *types.Signature:
		return e.emitDeclarationSignature(ty)
	case *types.Struct:
		fields := make([]any, ty.NumFields())
		for i := range fields {
			field := ty.Field(i)
			id, err := declarationObjectName(field)
			if err != nil {
				return nil, err
			}
			elem, err := e.emitDeclarationType(field.Type())
			if err != nil {
				return nil, err
			}
			// Tags are Go string bytes. JSON strings would replace invalid
			// UTF-8 and could identify distinct anonymous struct types.
			tag := []byte(ty.Tag(i))
			tagBytes := make([]int, len(tag))
			for j, b := range tag {
				tagBytes[j] = int(b)
			}
			fields[i] = map[string]any{"id": id, "type": elem,
				"embedded": field.Embedded(), "tagBytes": tagBytes}
		}
		return map[string]any{"kind": "struct", "fields": fields}, nil
	case *types.Interface:
		ty.Complete()
		if !ty.IsMethodSet() {
			return nil, unsup("declaration interface has non-method type-set terms")
		}
		methods := make([]*types.Func, ty.NumMethods())
		for i := range methods {
			methods[i] = ty.Method(i)
		}
		sort.Slice(methods, func(i, j int) bool { return methods[i].Id() < methods[j].Id() })
		entries := make([]any, len(methods))
		for i, method := range methods {
			id, err := declarationObjectName(method)
			if err != nil {
				return nil, err
			}
			sig, ok := method.Type().(*types.Signature)
			if !ok {
				return nil, unsup("declaration method %s has no signature", method.Name())
			}
			decl, err := e.emitDeclarationSignature(sig)
			if err != nil {
				return nil, err
			}
			entries[i] = map[string]any{"id": id, "signature": decl}
		}
		return map[string]any{"kind": "interface", "methods": entries}, nil
	default:
		return nil, unsup("declaration type is not a closed runtime type: %T (%s)", t, t)
	}
}
