// sync/atomic — the atomics arc, wave 1 (Q-ATOMIC, RULED [USER]
// 2026-09-02 option A′, `docs/2026-08-31_qrow-rulings.md` row 2;
// charter `docs/2026-09-01_qatomic-owner-proposal.md` §4; design note
// `docs/2026-09-03_atomics-w1-design.md`).
//
// THE LOWERING. A direct call of one of the modeled `sync/atomic`
// INTEGER functions — Load/Store/Add/Swap/CompareAndSwap over
// Int32/Int64/Uint32/Uint64/Uintptr — emits the wire node
//
//	{"expr":"atomic-op","op":<load|store|add|swap|cas>,
//	 "kind":<the integer's wire type>,"args":[addr, operands...],
//	 "resultTypes":[...]}
//
// which the decoder admits ONLY in the positions it admits `call`
// (an expression statement; the single RHS of an assignment) and
// lowers to `Stmt.atomicStmt` — ONE fused machine step at a
// scheduling boundary (Machine.lean `applyAtomicOp`). This is NOT shim
// injection under the D-002 freeze: no stdlib BODY is hand-modeled —
// the call plumbs to a machine op family whose semantics is argued
// from mem#atomic, exactly the shape of the `sync` ops (emit.go
// `emitSyncOpStmt`) — and the identity principle holds by
// construction: every spelling that lowers reaches the SAME op node
// (the direct call; the typed wrappers' methods, whose shadow-model
// bodies below are gc's own definitions and call the same functions).
//
// THE TYPED WRAPPERS (`atomic.Int32/Int64/Uint32/Uint64/Uintptr`) ride
// the E5-T shadow-model vehicle (importedmodel.go): a pinned mini
// `package atomic` (import path "sync/atomic") whose struct types and
// method bodies are TRANSCRIBED from go1.26.5's `sync/atomic/type.go`
// (`Load` = `LoadInt64(&x.v)`, …) — so a method call on a typed atomic
// lowers through the very same `atomic-op` node as the direct call
// (the ledger's recorded judgment: "typed variants ride the same
// lowering"). The model's function DECLARATIONS are bodyless (gc's
// own doc.go shape: the bodies are compiler intrinsics / assembly) and
// are the model's INTRINSIC surface — `lowerShadowModel` drops them
// before emission, admitting the bodyless shape ONLY for names in the
// atomics table below (anything else refuses the export). Upstream's
// `_ noCopy` / `_ align64` blank fields are omitted: blank fields
// carry no value, take no part in `==` (spec#Comparison_operators:
// "corresponding non-blank field values"), and `unsafe.Sizeof` is
// refused by the unsafe policy — no in-language observation reaches
// them; the empty composite literal `atomic.Int64{}` (the only legal
// cross-package literal — spec#Composite_literals, non-exported
// fields) lowers to the zero value of the model's def.
//
// FAIL-CLOSED RULES (every refusal names its cause and its wave):
//   - `And*`/`Or*` (the bitwise RMWs, Go 1.23): wave 2 — refused.
//   - `*Pointer` / `unsafe.Pointer` operands: outside the unsafe
//     policy — refused.
//   - `atomic.Value`, `atomic.Bool`, `atomic.Pointer[T]`: wave 2 —
//     refused at the TYPE choke point (`emitType`), so the red lands
//     at frontend-export with a named cause, never as a dangling stub.
//   - The FUNCTION-VALUE shape (`f := atomic.LoadInt64`), `go`/`defer`
//     of an atomic function: refused (the direct-call shape is the
//     whole surface — emitSelector's stdlib-selector refusal).
//   - Any other `sync/atomic` symbol: refused by name.
package main

import (
	"go/ast"
	"go/types"
	"strings"
)

// atomicPkgPath is the ONE package this file lowers.
const atomicPkgPath = "sync/atomic"

// atomicIntSuffixes maps the function-name suffix to the wire integer
// kind. `Uintptr` maps to `uintptr`, which the decoder (and the whole
// frontend, wire.go `emitBasic`) realizes as uint64 — the R1 pin.
var atomicIntSuffixes = map[string]string{
	"Int32":   "int32",
	"Int64":   "int64",
	"Uint32":  "uint32",
	"Uint64":  "uint64",
	"Uintptr": "uintptr",
}

// atomicOpPrefixes maps the function-name prefix to the wire op.
var atomicOpPrefixes = []struct{ prefix, op string }{
	{"CompareAndSwap", "cas"},
	{"Load", "load"},
	{"Store", "store"},
	{"Swap", "swap"},
	{"Add", "add"},
}

// atomicFuncOp classifies a `sync/atomic` package-level function by
// name: (op, kind, nil) for a wave-1 member; ("", "", refusal) for
// everything else, the refusal naming the member and its wave.
func atomicFuncOp(name string) (string, string, error) {
	for _, p := range atomicOpPrefixes {
		if !strings.HasPrefix(name, p.prefix) {
			continue
		}
		suffix := name[len(p.prefix):]
		if kind, ok := atomicIntSuffixes[suffix]; ok {
			return p.op, kind, nil
		}
		if suffix == "Pointer" {
			return "", "", unsup("sync/atomic.%s (the unsafe.Pointer family is outside the unsafe policy; the integer core is the modeled surface — atomics wave 1)", name)
		}
		return "", "", unsup("sync/atomic.%s (unknown integer kind suffix %q; the modeled kinds are Int32/Int64/Uint32/Uint64/Uintptr — atomics wave 1)", name, suffix)
	}
	if strings.HasPrefix(name, "And") || strings.HasPrefix(name, "Or") {
		return "", "", unsup("sync/atomic.%s (the bitwise And/Or RMW family is atomics WAVE 2 — not modeled yet)", name)
	}
	return "", "", unsup("sync/atomic.%s (outside the modeled sync/atomic surface: wave 1 lowers Load/Store/Add/Swap/CompareAndSwap over the integer kinds)", name)
}

// isAtomicFunc reports whether obj is a PACKAGE-LEVEL function of
// sync/atomic (methods key by receiver and never route here).
func isAtomicFunc(obj types.Object) (*types.Func, bool) {
	fn, ok := obj.(*types.Func)
	if !ok || fn.Pkg() == nil || fn.Pkg().Path() != atomicPkgPath {
		return nil, false
	}
	sig, ok := fn.Type().(*types.Signature)
	if !ok || sig.Recv() != nil {
		return nil, false
	}
	return fn, true
}

// emitAtomicCall lowers a direct call of a sync/atomic package-level
// function to the `atomic-op` wire node (effectful — the caller hoists
// it in expression position exactly like a call). The receiver of the
// classification is the resolved *types.Func, so the selector
// (`atomic.AddInt64`) and the bare-ident (inside the shadow model:
// `AddInt64`) spellings meet here identically.
func (e *emitter) emitAtomicCall(c *ast.CallExpr, fn *types.Func) (any, bool, error) {
	op, kind, err := atomicFuncOp(fn.Name())
	if err != nil {
		return nil, true, err
	}
	sig, _ := fn.Type().(*types.Signature)
	if sig == nil {
		return nil, true, unsup("sync/atomic.%s has no signature (fail closed)", fn.Name())
	}
	// A tuple-splat argument list `atomic.AddInt64(pair())` is legal Go
	// (spec#Calls: a multi-valued call as the sole argument) but outside
	// wave 1 — refuse naming THAT cause, not an arity mismatch (audit
	// fix L3a, 2026-09-03).
	if len(c.Args) == 1 {
		if inner, isCall := c.Args[0].(*ast.CallExpr); isCall {
			if _, isTup := e.goTypeOf(inner).(*types.Tuple); isTup {
				return nil, true, unsup("sync/atomic.%s with a tuple-splat argument list (a multi-valued call as the sole argument): atomics WAVE 2", fn.Name())
			}
		}
	}
	// The pinned signatures: addr first, then the value operands
	// (store/add/swap: one; cas: two; load: none). Anything else means
	// the toolchain's sync/atomic differs from the pin — refuse.
	wantArgs := map[string]int{"load": 1, "store": 2, "add": 2, "swap": 2, "cas": 3}[op]
	if sig.Params().Len() != wantArgs || len(c.Args) != wantArgs {
		return nil, true, unsup("sync/atomic.%s: expected %d operand(s), signature has %d and the call %d (pin drift or malformed call — fail closed)",
			fn.Name(), wantArgs, sig.Params().Len(), len(c.Args))
	}
	args, err := e.emitCallArgs(sig, c)
	if err != nil {
		return nil, true, err
	}
	resultTypes, err := e.emitResultTypes(sig)
	if err != nil {
		return nil, true, err
	}
	return map[string]any{"expr": "atomic-op", "op": op, "kind": intType(kind),
		"args": args, "resultTypes": resultTypes}, true, nil
}

// atomicTypedWrappers: the typed atomics of wave 1 (`type.go`'s
// integer structs) — the shadow model below declares exactly these.
var atomicTypedWrappers = map[string]bool{
	"Int32": true, "Int64": true, "Uint32": true, "Uint64": true, "Uintptr": true,
}

// atomicWave2Types: the sync/atomic types that refuse at the type
// choke point with a wave-2 cause.
var atomicWave2Types = map[string]string{
	"Value":   "atomic.Value stores interface values (boxing + gc's nil/inconsistent-type panics) — atomics WAVE 2",
	"Bool":    "atomic.Bool is a uint32-backed wrapper with a bool surface — atomics WAVE 2",
	"Pointer": "atomic.Pointer[T] is the unsafe.Pointer family — outside the unsafe policy (atomics WAVE 2 decides its vehicle)",
}

// atomicModelSrc is the pinned shadow model for the typed integer
// atomics — go1.26.5 `sync/atomic/type.go`, methods transcribed verbatim
// (the wave-1 members: Load/Store/Swap/CompareAndSwap/Add; `And`/`Or`
// are wave 2 and stay declaration-only stubs), minus the blank
// `noCopy`/`align64` fields (see the file header). The package-level
// functions are BODYLESS declarations — the intrinsic surface the
// emitter lowers at every call site; `lowerShadowModel` drops them.
const atomicModelSrc = `package atomic

// The sync/atomic typed-wrapper shadow model (atomics arc wave 1).
// Mirrors go/src/sync/atomic/type.go over the integer functions; see
// atomics.go for the fidelity argument and the modeled-method contract.

func LoadInt32(addr *int32) (val int32)
func LoadInt64(addr *int64) (val int64)
func LoadUint32(addr *uint32) (val uint32)
func LoadUint64(addr *uint64) (val uint64)
func LoadUintptr(addr *uintptr) (val uintptr)
func StoreInt32(addr *int32, val int32)
func StoreInt64(addr *int64, val int64)
func StoreUint32(addr *uint32, val uint32)
func StoreUint64(addr *uint64, val uint64)
func StoreUintptr(addr *uintptr, val uintptr)
func SwapInt32(addr *int32, new int32) (old int32)
func SwapInt64(addr *int64, new int64) (old int64)
func SwapUint32(addr *uint32, new uint32) (old uint32)
func SwapUint64(addr *uint64, new uint64) (old uint64)
func SwapUintptr(addr *uintptr, new uintptr) (old uintptr)
func CompareAndSwapInt32(addr *int32, old, new int32) (swapped bool)
func CompareAndSwapInt64(addr *int64, old, new int64) (swapped bool)
func CompareAndSwapUint32(addr *uint32, old, new uint32) (swapped bool)
func CompareAndSwapUint64(addr *uint64, old, new uint64) (swapped bool)
func CompareAndSwapUintptr(addr *uintptr, old, new uintptr) (swapped bool)
func AddInt32(addr *int32, delta int32) (new int32)
func AddInt64(addr *int64, delta int64) (new int64)
func AddUint32(addr *uint32, delta uint32) (new uint32)
func AddUint64(addr *uint64, delta uint64) (new uint64)
func AddUintptr(addr *uintptr, delta uintptr) (new uintptr)

// An Int32 is an atomic int32. The zero value is zero.
type Int32 struct {
	v int32
}

func (x *Int32) Load() int32 { return LoadInt32(&x.v) }

func (x *Int32) Store(val int32) { StoreInt32(&x.v, val) }

func (x *Int32) Swap(new int32) (old int32) { return SwapInt32(&x.v, new) }

func (x *Int32) CompareAndSwap(old, new int32) (swapped bool) {
	return CompareAndSwapInt32(&x.v, old, new)
}

func (x *Int32) Add(delta int32) (new int32) { return AddInt32(&x.v, delta) }

// An Int64 is an atomic int64. The zero value is zero.
type Int64 struct {
	v int64
}

func (x *Int64) Load() int64 { return LoadInt64(&x.v) }

func (x *Int64) Store(val int64) { StoreInt64(&x.v, val) }

func (x *Int64) Swap(new int64) (old int64) { return SwapInt64(&x.v, new) }

func (x *Int64) CompareAndSwap(old, new int64) (swapped bool) {
	return CompareAndSwapInt64(&x.v, old, new)
}

func (x *Int64) Add(delta int64) (new int64) { return AddInt64(&x.v, delta) }

// A Uint32 is an atomic uint32. The zero value is zero.
type Uint32 struct {
	v uint32
}

func (x *Uint32) Load() uint32 { return LoadUint32(&x.v) }

func (x *Uint32) Store(val uint32) { StoreUint32(&x.v, val) }

func (x *Uint32) Swap(new uint32) (old uint32) { return SwapUint32(&x.v, new) }

func (x *Uint32) CompareAndSwap(old, new uint32) (swapped bool) {
	return CompareAndSwapUint32(&x.v, old, new)
}

func (x *Uint32) Add(delta uint32) (new uint32) { return AddUint32(&x.v, delta) }

// A Uint64 is an atomic uint64. The zero value is zero.
type Uint64 struct {
	v uint64
}

func (x *Uint64) Load() uint64 { return LoadUint64(&x.v) }

func (x *Uint64) Store(val uint64) { StoreUint64(&x.v, val) }

func (x *Uint64) Swap(new uint64) (old uint64) { return SwapUint64(&x.v, new) }

func (x *Uint64) CompareAndSwap(old, new uint64) (swapped bool) {
	return CompareAndSwapUint64(&x.v, old, new)
}

func (x *Uint64) Add(delta uint64) (new uint64) { return AddUint64(&x.v, delta) }

// A Uintptr is an atomic uintptr. The zero value is zero.
type Uintptr struct {
	v uintptr
}

func (x *Uintptr) Load() uintptr { return LoadUintptr(&x.v) }

func (x *Uintptr) Store(val uintptr) { StoreUintptr(&x.v, val) }

func (x *Uintptr) Swap(new uintptr) (old uintptr) { return SwapUintptr(&x.v, new) }

func (x *Uintptr) CompareAndSwap(old, new uintptr) (swapped bool) {
	return CompareAndSwapUintptr(&x.v, old, new)
}

func (x *Uintptr) Add(delta uintptr) (new uintptr) { return AddUintptr(&x.v, delta) }
`

// atomicModelMethods: the methods the shadow model bodies (per typed
// wrapper); the rest of each exported method set (`And`, `Or`) lands
// as declaration-only stubs whose calls refuse.
var atomicModelMethods = map[string]bool{
	"Load": true, "Store": true, "Swap": true, "CompareAndSwap": true, "Add": true,
}

func init() {
	for name := range atomicTypedWrappers {
		modeledImportedTypes[atomicPkgPath+"."+name] = &importedTypeModel{
			pkgPath:   atomicPkgPath,
			pkgName:   "atomic",
			src:       atomicModelSrc,
			modeled:   atomicModelMethods,
			intrinsic: true,
		}
	}
}

// atomicIntrinsicDecl reports whether a BODYLESS package-level function
// declaration of the shadow model is an admitted intrinsic — exactly
// the wave-1 table (`atomicFuncOp` classifies it). Anything else
// bodyless refuses the model's lowering.
func atomicIntrinsicDecl(d *ast.FuncDecl) bool {
	if d.Recv != nil || d.Body != nil {
		return false
	}
	_, _, err := atomicFuncOp(d.Name.Name)
	return err == nil
}

// atomicStubRefusal names the refusal a declaration-only stub of a typed
// wrapper's UNMODELED method carries (`And`/`Or` — the bitwise RMW
// family): the wave-2 cause the design note §1 claims, not the generic
// imported-method text (audit fix L3b, 2026-09-03). ok=false for any
// other type/method (the generic text applies).
func atomicStubRefusal(qname, method string) (string, bool) {
	if !strings.HasPrefix(qname, atomicPkgPath+".") || !atomicTypedWrappers[qname[len(atomicPkgPath)+1:]] {
		return "", false
	}
	if method == "And" || method == "Or" {
		return qname + "." + method + " (the bitwise And/Or RMW family is atomics WAVE 2 — not modeled yet; declaration-only stub: satisfaction answers, calls fail closed)", true
	}
	return "", false
}
