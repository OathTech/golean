package main

// uintptrid.go (release-readiness item 26, BUG-123): every position where a
// uintptr-mentioning type is BOXED into an interface, or named as a type
// assertion / type-switch TARGET, refuses by name through the standing
// per-declaration quarantine; width-only uses lower. The six refusing
// shapes are the release-trust review's R1 probes
// (docs/2026-10-12_release-trust-review.md), the rest the assignability
// positions of spec#Assignability and the comparison / switch / range /
// panic / append / generic / method-set / package-initializer shapes.

import (
	"strings"
	"testing"
)

const uintptrRefusalMark = "uintptr identity is unmodeled (lowered as uint64)"

func TestUintptrIdentityRefusesByName(t *testing.T) {
	cases := map[string]struct{ src, construct string }{
		// --- the review's six probes ---
		"r1-assert": {`package main
func subject() bool { var x any = uintptr(1); _, ok := x.(uint64); return ok }
`, "variable declaration boxes uintptr into any"},
		"r1-equal": {`package main
func subject() bool { return any(uintptr(1)) == any(uint64(1)) }
`, "conversion boxes uintptr into any"},
		"r1-switch": {`package main
func subject() int {
	var x any = uintptr(1)
	switch x.(type) {
	case uint64:
		return 64
	case uintptr:
		return 1
	}
	return 0
}
`, "variable declaration boxes uintptr into any"},
		"r1-map-key": {`package main
func subject() int { return len(map[any]int{uintptr(1): 7, uint64(1): 9}) }
`, "map literal key boxes uintptr into any"},
		"r1-slice-assert": {`package main
func subject() bool { var x any = []uintptr{1}; _, ok := x.([]uint64); return ok }
`, "variable declaration boxes []uintptr into any"},
		"r1-pointer-assert": {`package main
func subject() bool { n := uintptr(1); var x any = &n; _, ok := x.(*uint64); return ok }
`, "variable declaration boxes *uintptr into any"},
		// --- rule (b): targets mentioning uintptr, over a boxed uint64 ---
		"target-assert": {`package main
func subject() bool { var x any = uint64(1); _, ok := x.(uintptr); return ok }
`, "type assertion to uintptr"},
		"target-assert-slice": {`package main
func subject() bool { var x any = []uint64{1}; _, ok := x.([]uintptr); return ok }
`, "type assertion to []uintptr"},
		"target-switch-case": {`package main
func subject() int {
	var x any = uint64(1)
	switch x.(type) {
	case *uintptr:
		return 1
	}
	return 0
}
`, "type switch case *uintptr"},
		"target-single-assert": {`package main
func subject() int { var x any = uint64(1); return int(x.(uintptr)) }
`, "type assertion to uintptr"},
		// --- rule (a) at every assignability position ---
		"assign-existing": {`package main
func subject() int { var x any; x = uintptr(2); _ = x; return 1 }
`, "assignment boxes uintptr into any"},
		"call-arg": {`package main
func sink(v any) int { _ = v; return 1 }
func subject() int { return sink(uintptr(3)) }
`, "call argument boxes uintptr into any"},
		"call-variadic": {`package main
func sink(vs ...any) int { return len(vs) }
func subject() int { return sink(1, uintptr(3)) }
`, "call argument boxes uintptr into any"},
		"call-interface-method": {`package main
type I interface{ M(v any) int }
type T struct{}
func (T) M(v any) int { _ = v; return 1 }
func subject() int { var i I = T{}; return i.M(uintptr(1)) }
`, "call argument boxes uintptr into any"},
		"return": {`package main
func subject() any { return uintptr(4) }
`, "return boxes uintptr into any"},
		"return-funclit": {`package main
func subject() int {
	f := func() any { return uintptr(4) }
	_ = f()
	return 1
}
`, "return boxes uintptr into any"},
		"struct-field": {`package main
type S struct{ f any }
func subject() int { s := S{f: uintptr(1)}; _ = s; return 1 }
`, "struct literal field f boxes uintptr into any"},
		"slice-element": {`package main
func subject() int { return len([]any{uintptr(1)}) }
`, "slice literal element boxes uintptr into any"},
		"nested-elided-literal": {`package main
type S struct{ f any }
func subject() int { return len([]S{{uintptr(1)}}) }
`, "struct literal field f boxes uintptr into any"},
		"send": {`package main
func subject() int { ch := make(chan any, 1); ch <- uintptr(1); return len(ch) }
`, "send boxes uintptr into any"},
		"map-index": {`package main
func subject() int { m := map[any]int{}; m[uintptr(1)] = 7; return len(m) }
`, "map index key boxes uintptr into any"},
		"compare-interface": {`package main
func subject() bool { var x any = uint64(1); return x == uintptr(1) }
`, "comparison operand boxes uintptr into any"},
		"switch-case-interface-tag": {`package main
func subject() int {
	var x any = uint64(1)
	switch x {
	case uintptr(1):
		return 1
	}
	return 0
}
`, "switch case against an interface tag boxes uintptr into any"},
		"panic-value": {`package main
func subject() (r int) {
	defer func() { if recover() != nil { r = 1 } }()
	panic(uintptr(1))
}
`, "panic value boxes uintptr into any"},
		"append-element": {`package main
func subject() int { var s []any; s = append(s, uintptr(1)); return len(s) }
`, "append element boxes uintptr into any"},
		"range-assign": {`package main
func subject() int { var v any; for _, v = range []uintptr{1} { _ = v }; return 1 }
`, "range value assignment boxes uintptr into any"},
		"multi-value-call": {`package main
func two() (uintptr, int) { return 1, 2 }
func subject() int { var a any; var b int; a, b = two(); _ = a; return b }
`, "multi-value assignment boxes uintptr into any"},
		"comma-ok-receive": {`package main
func subject() int { ch := make(chan uintptr, 1); ch <- 1; var v any; var ok bool; v, ok = <-ch; _, _ = v, ok; return 1 }
`, "multi-value assignment boxes uintptr into any"},
		"defined-over-uintptr": {`package main
type U uintptr
func subject() int { var x any = U(1); _ = x; return 1 }
`, "variable declaration boxes main.U into any"},
		"method-set-mentions": {`package main
type T struct{}
func (T) P() uintptr { return 1 }
func subject() int { var x any = T{}; _ = x; return 1 }
`, "variable declaration boxes main.T into any"},
		"struct-with-field": {`package main
type S struct{ p uintptr }
func subject() int { var x any = S{}; _ = x; return 1 }
`, "variable declaration boxes main.S into any"},
		"func-type-mentions": {`package main
func subject() int { var x any = func(uintptr) {}; _ = x; return 1 }
`, "variable declaration boxes func(uintptr) into any"},
		"interface-requirement-target": {`package main
type P interface{ P() uintptr }
func subject() bool { var x any = 1; _, ok := x.(P); return ok }
`, "type assertion to main.P"},
	}
	for name, c := range cases {
		t.Run(name, func(t *testing.T) {
			program, err := emitSource(t, c.src)
			if err != nil {
				t.Fatalf("the per-declaration quarantine keeps the export OK: %v", err)
			}
			reason := stubReason(t, program, "subject")
			if reason == "" {
				t.Fatalf("an identity-bearing uintptr position must quarantine the declaration by name (BUG-123):\n%s", mustJSON(t, program))
			}
			for _, want := range []string{uintptrRefusalMark, c.construct, "main.go:", "release-readiness item 26", "BUG-123"} {
				if !strings.Contains(reason, want) {
					t.Errorf("the refusal must carry %q:\n%s", want, reason)
				}
			}
		})
	}
}

// A generic function's stencil is scanned under its instantiation: the
// template `return x` boxes T into any only when T mentions uintptr.
func TestUintptrIdentityStencilScannedUnderInstantiation(t *testing.T) {
	src := `package main
func box[T any](x T) any { return x }
func subject() int { _ = box(uintptr(1)); return 1 }
func control() int { _ = box(uint64(1)); return 1 }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	names := funcNames(program)
	refused, lowered := 0, 0
	for name, fn := range names {
		if !strings.HasPrefix(name, "box") {
			continue
		}
		reason, _ := fn["unsupported"].(string)
		switch {
		case strings.Contains(name, "uintptr"):
			if !strings.Contains(reason, uintptrRefusalMark) || !strings.Contains(reason, "return boxes uintptr into any") {
				t.Errorf("the uintptr stencil %s must refuse by name, got %q", name, reason)
			}
			refused++
		default:
			if reason != "" {
				t.Errorf("the uint64 stencil %s must lower, got %q", name, reason)
			}
			lowered++
		}
	}
	if refused != 1 || lowered != 1 {
		t.Fatalf("expected one refused and one lowered stencil, got refused=%d lowered=%d (%v)", refused, lowered, names)
	}
	if r := stubReason(t, program, "subject"); r != "" {
		t.Errorf("the caller lowers (the stencil carries the refusal): %q", r)
	}
	if r := stubReason(t, program, "control"); r != "" {
		t.Errorf("the control lowers: %q", r)
	}
}

// A package-level initializer that boxes a uintptr is the initializer's
// own named refusal (the H-11 dry run), never a silent `$pkginit` box.
func TestUintptrIdentityPackageInitializerRefuses(t *testing.T) {
	src := `package main
var g any = uintptr(1)
func subject() int { _ = g; return 1 }
`
	program, err := emitSource(t, src)
	if err != nil {
		if !strings.Contains(err.Error(), uintptrRefusalMark) {
			t.Fatalf("a whole-export refusal must still name the cause: %v", err)
		}
		return
	}
	// Quarantined initializer: the reader of its poisoned cell refuses by
	// the initializer's cause.
	reason := stubReason(t, program, "subject")
	if !strings.Contains(reason, uintptrRefusalMark) {
		t.Fatalf("the reader of a boxing initializer's cell must carry the initializer's named refusal, got %q\n%s", reason, mustJSON(t, program))
	}
}

// Width-only uses keep lowering: arithmetic, conversions, storage, pointers
// and slices of uintptr passed to NON-interface parameters, map keys of
// type uintptr, println, comparisons between uintptr values, and interface
// values that never hold one.
func TestUintptrIdentityWidthOnlyLowers(t *testing.T) {
	cases := map[string]string{
		"arith-and-convert": `package main
func subject() int { var p uintptr = 40; p += uintptr(2); q := uint64(p) * 3; return int(q) + int(p) }
`,
		"pointer-param": `package main
func bump(p *uintptr) { *p++ }
func subject() int { var u uintptr; bump(&u); return int(u) }
`,
		"slice-and-map": `package main
func subject() int { s := []uintptr{1, 2}; m := map[uintptr]int{s[0]: 1}; return len(s) + m[1] }
`,
		"println": `package main
func subject() int { var u uintptr = 12; println(u); return int(u) }
`,
		"compare-same-type": `package main
func subject() bool { return uintptr(1) == uintptr(2) }
`,
		"struct-storage": `package main
type S struct{ p uintptr }
func subject() int { s := S{p: 3}; s.p++; return int(s.p) }
`,
		"interface-without-uintptr": `package main
func subject() bool { var x any = uint64(1); _, ok := x.(uint64); return ok }
`,
		"append-same-type": `package main
func subject() int { var s []uintptr; s = append(s, 1); return len(s) }
`,
		"range-define": `package main
func subject() int { n := 0; for _, v := range []uintptr{1, 2} { n += int(v) }; return n }
`,
		"funclit-returns-uintptr": `package main
func subject() int { f := func() uintptr { return 5 }; return int(f()) }
`,
		"generic-same-type": `package main
func id[T any](x T) T { return x }
func subject() int { return int(id(uintptr(7))) }
`,
	}
	for name, src := range cases {
		t.Run(name, func(t *testing.T) {
			program, err := emitSource(t, src)
			if err != nil {
				t.Fatalf("export must succeed: %v", err)
			}
			if r := stubReason(t, program, "subject"); r != "" {
				t.Fatalf("a width-only use of uintptr must lower, got %q", r)
			}
		})
	}
}

// A named type declared outside the source packages is judged by its
// METHOD SET only: `*sync.Map` (a `uintptr` hash seed inside, never on
// the wire; no uintptr in any method signature) is NOT this refusal,
// `*atomic.Uintptr` (`Load() uintptr`, an interface requirement the
// decoder would collapse) IS.
func TestUintptrIdentityOpaqueImportedTypeByMethodSet(t *testing.T) {
	program, err := emitSource(t, `package main
import "sync"
func subject() int { var m sync.Map; var x any = &m; _ = x; return 1 }
`)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	if r := stubReason(t, program, "subject"); strings.Contains(r, uintptrRefusalMark) {
		t.Errorf("an opaque stdlib type's real fields must not count (its model has none on the wire), got %q", r)
	}
	program, err = emitSource(t, `package main
import "sync/atomic"
func subject() int { var au atomic.Uintptr; var x any = &au; _ = x; return 1 }
`)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	if r := stubReason(t, program, "subject"); !strings.Contains(r, uintptrRefusalMark) || !strings.Contains(r, "boxes *atomic.Uintptr into any") {
		t.Errorf("a method set mentioning uintptr is an interface requirement the decoder collapses: must refuse by name, got %q", r)
	}
	// The raft subject's shape (`raft.DefaultLogger` embeds `*log.Logger`,
	// boxed into `raft.Logger`): `log.Logger`'s UNEXPORTED `output(pc
	// uintptr, …)` is nameable by no requirement outside package log and
	// must not count — the twin-wire pin (scripts/check-frontend-pins)
	// caught the first cut counting it.
	program, err = emitSource(t, `package main
import "log"
type Logger interface{ Printf(string, ...any) }
type DefaultLogger struct{ *log.Logger; debug bool }
func subject() int { var l Logger = &DefaultLogger{}; _ = l; return 1 }
`)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	if r := stubReason(t, program, "subject"); strings.Contains(r, uintptrRefusalMark) {
		t.Errorf("an opaque type's unexported method must not count (no requirement outside its package can name it), got %q", r)
	}
}

// A BODYLESS declaration (an assembly-backed function, the shape
// source-through stdlib units carry) has nothing to scan: the pre-pass must
// not crash on its typed-nil body (the first cut did, on the
// stdlib-source/frontier package: the whole package failed at
// frontend-export and its PASS row flipped — a crash is never a named
// refusal).
func TestUintptrIdentityBodylessDeclarationIsNotScanned(t *testing.T) {
	src := `package main
func asmBacked(x uintptr) uintptr
func subject() int { return 1 }
`
	program, err := emitSource(t, src)
	if err != nil {
		if strings.Contains(err.Error(), uintptrRefusalMark) {
			t.Fatalf("a bodyless declaration must not carry the uintptr refusal: %v", err)
		}
		return // the emitter's own bodyless refusal, if any, is not this rule's
	}
	if r := stubReason(t, program, "subject"); r != "" {
		t.Errorf("subject must lower, got %q", r)
	}
	if r := stubReason(t, program, "asmBacked"); strings.Contains(r, uintptrRefusalMark) {
		t.Errorf("a bodyless declaration must not carry the uintptr refusal, got %q", r)
	}
}

// A sibling declaration's own refusal is still reported beside a uintptr
// refusal (the quarantine is per declaration, not whole-export).
func TestUintptrIdentityDoesNotMaskSibling(t *testing.T) {
	src := `package main
import "os"
func boxer() int { var x any = uintptr(1); _ = x; return 1 }
func exiter() { os.Exit(3) }
func fine() int { return 2 }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	if r := stubReason(t, program, "boxer"); !strings.Contains(r, uintptrRefusalMark) {
		t.Errorf("boxer must refuse by name, got %q", r)
	}
	if r := stubReason(t, program, "exiter"); r == "" || strings.Contains(r, uintptrRefusalMark) {
		t.Errorf("exiter must carry its own refusal, got %q", r)
	}
	if r := stubReason(t, program, "fine"); r != "" {
		t.Errorf("fine must lower, got %q", r)
	}
}
