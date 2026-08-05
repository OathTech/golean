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
// rune→int32), "interface {}" for the empty interface — so Go panic texts
// contain the key VERBATIM and TypeId.unqualified reproduces
// reflect.Type.Name() (the observation channel's contract).

import (
	"go/types"
	"strings"
)

// monoRegistryCap bounds the number of distinct mangled keys (decision
// §9.4): go/types' mono check guarantees the instantiation closure is
// FINITE for every program our conf.Check accepts, but not small — a
// multiplicative instantiation chain stays finite while growing beyond any
// constant. Exceeding the cap fails the export loudly; never silent
// truncation.
const monoRegistryCap = 10000

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
// parameters) fail closed: none of them can reach a supported wire type
// either, and refusing here keeps the key space inside the injectivity
// argument.
func (e *emitter) renderTypeArg(t types.Type) (string, error) {
	switch ty := t.(type) {
	case *types.Basic:
		return renderBasicArg(ty)
	case *types.Named:
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
