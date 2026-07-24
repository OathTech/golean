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

	// Bare-`break` target tracking (W2): Go's bare break targets the
	// nearest enclosing for/switch/select; the switch desugaring (an
	// if-chain) has no native break target, so a bare break whose target
	// is a switch fails closed until the flag desugaring lands (slice 2).
	breakStack []string
}

// emptyStructName is the canonical GoCore type name for the empty struct
// struct{} (the set-value idiom map[K]struct{}).
const emptyStructName = "struct{}"

// unsupported is returned when a construct is not yet modeled. The pipeline
// fails closed: the emitter never approximates.
type unsupported struct{ what string }

func (u unsupported) Error() string { return "native frontend unsupported: " + u.what }

func unsup(format string, args ...any) error {
	return unsupported{fmt.Sprintf(format, args...)}
}

// ---- types ----

func (e *emitter) emitType(t types.Type) (any, error) {
	switch ty := t.(type) {
	case *types.Basic:
		return e.emitBasic(ty)
	case *types.Named:
		obj := ty.Obj()
		// A named type whose underlying is an interface is an interface type;
		// otherwise it is a defined type. GoCore distinguishes the two.
		if _, ok := ty.Underlying().(*types.Interface); ok {
			return map[string]any{"kind": "interface", "name": obj.Name()}, nil
		}
		return map[string]any{"kind": "named", "name": obj.Name()}, nil
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
			return map[string]any{"kind": "interface", "name": "any"}, nil
		}
		return nil, unsup("anonymous non-empty interface type %s", ty)
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
	// Untyped constants carry their default type at use sites; go/types has
	// usually already resolved them, but guard the bare kinds.
	case types.UntypedInt:
		return intType("int"), nil
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
