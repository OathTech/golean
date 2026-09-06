package main

// Positive declaration facts for I1. This serializer does not ask whether a
// type has an executable representation, register an opaque TypeDef, or inspect
// a function body. Its output is a separate schema; it is not accepted by the
// current executable-type decoder. Connecting it to package admission and the
// clean code table is a subsequent change.

import (
	"go/types"
	"sort"
)

// A Go identifier's package participates in identity only when unexported.
// This is used for anonymous struct fields and interface methods, not for
// nominal type declarations, which always have their own TypeId.
func declarationObjectName(obj types.Object) map[string]any {
	pkg := ""
	if !obj.Exported() && obj.Pkg() != nil {
		pkg = obj.Pkg().Path()
	}
	return map[string]any{"name": obj.Name(), "package": pkg}
}

func (e *emitter) emitDeclarationTuple(tuple *types.Tuple) ([]any, error) {
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
func (e *emitter) emitDeclarationSignature(sig *types.Signature) (map[string]any, error) {
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

func (e *emitter) emitDeclarationType(t types.Type) (any, error) {
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
		if pkg := obj.Pkg(); pkg != nil && obj.Parent() != pkg.Scope() {
			if _, ok := e.localTypeOrdinal(obj); !ok {
				return nil, unsup("declaration identity has no local type ordinal: %s", obj.Name())
			}
		}
		id := e.qualifiedTypeName(obj)
		if e.substErr != nil {
			return nil, e.substErr
		}
		if e.declarationNominals != nil {
			arity := ty.Origin().TypeParams().Len()
			if old, present := e.declarationNominals[id]; present && old != arity {
				return nil, unsup("declaration origin %s has conflicting arities %d and %d", id, old, arity)
			}
			e.declarationNominals[id] = arity
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
			fields[i] = map[string]any{"id": declarationObjectName(field), "type": elem,
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
			sig, ok := method.Type().(*types.Signature)
			if !ok {
				return nil, unsup("declaration method %s has no signature", method.Name())
			}
			decl, err := e.emitDeclarationSignature(sig)
			if err != nil {
				return nil, err
			}
			entries[i] = map[string]any{"id": declarationObjectName(method), "signature": decl}
		}
		return map[string]any{"kind": "interface", "methods": entries}, nil
	default:
		return nil, unsup("declaration type is not a closed runtime type: %T (%s)", t, t)
	}
}
