package main

// Unit tests for FR-24 (2026-09-04, lane fr24): a package-level var whose
// TYPE does not lower is POISONED per declaration instead of refusing the
// whole export. The differential corpus pins the OBSERVABLE contract
// (init/user-var-type-unlowerable, init/library-var-type-poisoned,
// init/library-var-type-unlowerable); these pin what the differential
// structurally cannot see: the cell is re-typed `$poisoned` (seedable, gid
// kept), the placeholder TypeDef exists, every reference shape (method
// call, address-of, read) lands as an H-3 stub NAMING the var, its type and
// emitType's cause, a healthy sibling lowers, the initializer order is
// untouched, and the residual shapes (an initialized poisoned var in a user
// package; a struct FIELD of the type) still refuse naming their cause.

import (
	"strings"
	"testing"
)

const typePoisonSrc = `package main

import "sync"

var seq []string

func note(s string) int { seq = append(seq, s); return len(seq) }

var a = note("a")
var cache sync.Map
var b = note("b")

func unused() int { return a*10 + b }

func used() int {
	cache.Store(1, 41)
	v, ok := cache.Load(1)
	if !ok {
		return -1
	}
	return v.(int) + 1
}

func keep(p any) bool { return p != nil }

// Address-of THROUGH a call: a local ` + "`p := &cache`" + ` would refuse on p's own
// unlowerable type (*sync.Map) before the operand reaches globalAddr — the
// same fail-closed stub with the type's text, not the var's name. This
// shape is the one that names the var.
func addrOf() int {
	if !keep(&cache) {
		return -1
	}
	return 1
}

func main() { println(unused(), used(), addrOf()) }
`

func TestUnlowerableTypedGlobalPoisonsPerDeclaration(t *testing.T) {
	program, err := emitSource(t, typePoisonSrc)
	if err != nil {
		t.Fatalf("a package-level var of an unlowerable TYPE must poison per declaration, not refuse the export (FR-24): %v", err)
	}
	if n := pkginitStmtCount(t, program); n != 2 {
		t.Fatalf("$pkginit carries %d statements, want 2 (a, b — the poisoned var has no initializer; seq has none)", n)
	}
	g := globalByName(program, "cache")
	if g == nil {
		t.Fatalf("poisoned var cache dropped from the globals table (gid density)")
	}
	if got := namedTypeName(g["type"]); got != poisonedCellTypeId {
		t.Fatalf("poisoned var cache seeds as %v, want named %s (a sync.Map cell has no machine default; the placeholder is what the machine holds)", g["type"], poisonedCellTypeId)
	}
	if td := typeDefByName(program, poisonedCellTypeId); td == nil {
		t.Fatalf("no %s TypeDef", poisonedCellTypeId)
	}
	for _, name := range []string{"a", "b"} {
		if hg := globalByName(program, name); hg == nil || namedTypeName(hg["type"]) == poisonedCellTypeId {
			t.Fatalf("healthy var %s was re-typed: %v", name, hg)
		}
	}
	for _, fn := range []string{"used", "addrOf"} {
		f := funcByName(program, fn)
		if f == nil {
			t.Fatalf("%s missing from the function table", fn)
		}
		r, _ := f["unsupported"].(string)
		for _, want := range []string{"package-level var", "cache", "sync.Map", "only Mutex/RWMutex/WaitGroup/Once", "FR-24"} {
			if !strings.Contains(r, want) {
				t.Fatalf("%s must be a stub naming %q (var, type, cause, row), got %q", fn, want, r)
			}
		}
	}
	if f := funcByName(program, "unused"); f == nil || f["unsupported"] != nil {
		t.Fatalf("unused must lower: %v", f)
	}
}

func TestUnlowerableTypedGlobalWithInitializer(t *testing.T) {
	// The TYPE poison arms in collectGlobals; the dry-run pre-pass then sees
	// the initializer's assignment fail at the poisoned target and decides
	// by the LANDED H-11 rule, unchanged:
	//   (a) `var cache = sync.Map{}` — an element-free composite literal is
	//       on the effect-isolated positive list (no call, no effect, no
	//       panic), so the initializer is SKIPPED and the var stays
	//       poisoned — sound: a zero-value store into an unreachable cell;
	//   (b) `var cache = mk()` — a call to a callee that is not an
	//       init-callee register row is NOT isolatable, so the WHOLE export
	//       refuses, naming the declaration (the F1/F1b direction).
	const isolated = `package main

import "sync"

var cache = sync.Map{}

func unrelated() int { return 7 }

func main() { println(unrelated()) }
`
	program, err := emitSource(t, isolated)
	if err != nil {
		t.Fatalf("(a) an element-free composite-literal initializer is effect-isolated; the var must poison, not kill the export: %v", err)
	}
	g := globalByName(program, "cache")
	if g == nil || namedTypeName(g["type"]) != poisonedCellTypeId {
		t.Fatalf("(a) cache must be a %s cell, got %v", poisonedCellTypeId, g)
	}
	if n := pkginitStmtCount(t, program); n != 0 {
		t.Fatalf("(a) $pkginit carries %d statements, want 0 (the skipped initializer)", n)
	}
	const effectful = `package main

import "sync"

var seq int

func mk() sync.Map { seq++; return sync.Map{} }

var cache = mk()

func unrelated() int { return 7 }

func main() { println(unrelated()) }
`
	_, err = emitSource(t, effectful)
	if err == nil {
		t.Fatalf("(b) an initializer CALLING a non-register callee must not be silently skipped (its effect on seq is observable)")
	}
	for _, want := range []string{"initializer of cache", "sync.Map", "FR-22"} {
		if !strings.Contains(err.Error(), want) {
			t.Fatalf("(b) whole-export refusal must name %q: %v", want, err)
		}
	}
}

func TestStructFieldOfUnlowerableTypeStillRefusesExport(t *testing.T) {
	// The var's own type is a lowerable `named` reference, so FR-24's poison
	// never arms; the TypeDef pass refuses at the FIELD. Recorded as the
	// residual (its own frontier row), pinned here so a future change of
	// the blast radius is a deliberate one.
	const src = `package main

import "sync"

type holder struct {
	m sync.Map
	n int
}

var h holder

func unrelated() int { return 7 }

func main() { h.n = 1; println(unrelated(), h.n) }
`
	_, err := emitSource(t, src)
	if err == nil {
		t.Fatalf("a struct TypeDef with an unlowerable field is a whole-export refusal today (rowed); a per-declaration answer here is a design change that must be recorded")
	}
	if !strings.Contains(err.Error(), "sync.Map") {
		t.Fatalf("the refusal must name the field type: %v", err)
	}
}
