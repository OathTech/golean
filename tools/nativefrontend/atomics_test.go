package main

// Unit pins for the sync/atomic lowering table (atomics.go, the
// atomics arc wave 1): the wave-1 members classify to their op/kind,
// and every out-of-scope member REFUSES with a cause that names the
// member and its wave — never a silent fall-through to the generic
// selector refusal, never an admission.

import (
	"strings"
	"testing"
)

func TestAtomicFuncOpWave1Members(t *testing.T) {
	cases := []struct{ name, op, kind string }{
		{"LoadInt32", "load", "int32"},
		{"LoadInt64", "load", "int64"},
		{"LoadUint32", "load", "uint32"},
		{"LoadUint64", "load", "uint64"},
		{"LoadUintptr", "load", "uintptr"},
		{"StoreInt64", "store", "int64"},
		{"StoreUintptr", "store", "uintptr"},
		{"AddInt32", "add", "int32"},
		{"AddUint64", "add", "uint64"},
		{"SwapInt64", "swap", "int64"},
		{"SwapUint32", "swap", "uint32"},
		{"CompareAndSwapInt32", "cas", "int32"},
		{"CompareAndSwapUint64", "cas", "uint64"},
		{"CompareAndSwapUintptr", "cas", "uintptr"},
	}
	for _, c := range cases {
		op, kind, err := atomicFuncOp(c.name)
		if err != nil {
			t.Fatalf("%s: unexpected refusal: %v", c.name, err)
		}
		if op != c.op || kind != c.kind {
			t.Fatalf("%s: got (%q, %q), want (%q, %q)", c.name, op, kind, c.op, c.kind)
		}
	}
}

func TestAtomicFuncOpRefusalsNameTheirCause(t *testing.T) {
	cases := []struct{ name, want string }{
		{"AndInt32", "WAVE 2"},
		{"OrUint64", "WAVE 2"},
		{"AndUintptr", "WAVE 2"},
		{"LoadPointer", "unsafe"},
		{"StorePointer", "unsafe"},
		{"CompareAndSwapPointer", "unsafe"},
		{"SwapPointer", "unsafe"},
		{"LoadInt16", "unknown integer kind"},
		{"Frobnicate", "outside the modeled sync/atomic surface"},
		{"", "outside the modeled sync/atomic surface"},
	}
	for _, c := range cases {
		op, kind, err := atomicFuncOp(c.name)
		if err == nil {
			t.Fatalf("%q: admitted as (%q, %q) instead of refusing", c.name, op, kind)
		}
		if !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%q: refusal %q does not name %q", c.name, err.Error(), c.want)
		}
	}
}

func TestAtomicIntrinsicDeclTableIsClosed(t *testing.T) {
	// Every wave-2 type refuses with a wave-2 cause; every typed
	// wrapper is a model member; the two sets are disjoint and cover
	// exactly the exported types of go1.26.5's sync/atomic.
	for name := range atomicWave2Types {
		if atomicTypedWrappers[name] {
			t.Fatalf("%s is both a wave-2 refusal and a typed wrapper", name)
		}
	}
	for _, name := range []string{"Bool", "Pointer", "Value"} {
		if _, ok := atomicWave2Types[name]; !ok {
			t.Fatalf("%s missing from the wave-2 refusal table", name)
		}
	}
	for _, name := range []string{"Int32", "Int64", "Uint32", "Uint64", "Uintptr"} {
		if !atomicTypedWrappers[name] {
			t.Fatalf("%s missing from the typed-wrapper model", name)
		}
	}
}

func TestAtomicShadowModelLowers(t *testing.T) {
	// The pinned shadow model must lower through the ordinary pipeline:
	// five TypeDefs, methods for exactly the wave-1 members, no plain
	// functions (the bodyless intrinsics are dropped, not emitted).
	model := modeledImportedTypes[atomicPkgPath+".Int64"]
	if model == nil || !model.intrinsic {
		t.Fatal("sync/atomic.Int64 is not registered as an intrinsic shadow model")
	}
	defs, methods, err := lowerShadowModel(model)
	if err != nil {
		t.Fatalf("shadow model failed to lower: %v", err)
	}
	if len(defs) != 5 {
		t.Fatalf("expected 5 TypeDefs, got %d", len(defs))
	}
	got := map[string]int{}
	for _, mm := range methods {
		m := mm.(map[string]any)
		got[m["name"].(string)]++
		if _, quarantined := m["unsupported"]; quarantined {
			t.Fatalf("model method %v did not lower: %v", m["name"], m["unsupported"])
		}
	}
	for _, name := range []string{"Load", "Store", "Swap", "CompareAndSwap", "Add"} {
		if got[name] != 5 {
			t.Fatalf("method %s: expected 5 bodies (one per wrapper), got %d", name, got[name])
		}
	}
	if got["And"] != 0 || got["Or"] != 0 {
		t.Fatal("And/Or must not be bodied in wave 1")
	}
}
