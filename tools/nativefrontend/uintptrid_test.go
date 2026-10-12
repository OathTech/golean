package main

// uintptrid.go (release-readiness item 26, BUG-124): every position where a
// uintptr-mentioning type is BOXED into an interface, or named as a type
// assertion / type-switch TARGET, refuses by name through the standing
// per-declaration quarantine; width-only uses lower, and a NAMED concrete
// type (nominal on the machine) boxes and asserts correctly unless its
// method set mentions uintptr. The six refusing shapes are the
// release-trust review's R1 probes (docs/2026-10-12_release-trust-review.md),
// the rest the assignability positions of spec#Assignability and the
// comparison / switch / range / panic / append / generic / method-set /
// package-initializer shapes. COUNT DERIVATION (the one every record cites):
// the entries of `uintptrRefusingShapes` (34, the six probes among them)
// plus the separately pinned refusing shapes (3: the generic stencil at
// uintptr, the package-level initializer, the opaque `*atomic.Uintptr`) =
// 37 refusing shapes; the controls are `uintptrWidthOnlyShapes` (18: 12
// width-only, 6 nominal) plus the separately pinned lowering shapes (7: the
// uint64 stencil, the width-only generic stencils incl. a method stencil,
// the stdlib generics, `*sync.Map`, the `*log.Logger` embedding, the
// bodyless declaration, the blank package-level box) = 25 lowering shapes.

import (
	"strings"
	"testing"
)

const uintptrRefusalMark = "uintptr identity is unmodeled (lowered as uint64)"

// uintptrRefusingShapes: name → (source, the construct phrase the refusal
// must carry). Every entry quarantines `subject` by name.
var uintptrRefusingShapes = map[string]struct{ src, construct string }{
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
	"local-blank-var": {`package main
func subject() int { var _ any = uintptr(1); return 1 }
`, "variable declaration boxes uintptr into any"},
	// --- named types: only through the METHOD SET (nominal otherwise) ---
	"method-set-mentions": {`package main
type T struct{}
func (T) P() uintptr { return 1 }
func subject() int { var x any = T{}; _ = x; return 1 }
`, "variable declaration boxes main.T into any"},
	"promoted-method-set": {`package main
type T struct{}
func (T) P() uintptr { return 1 }
type Out struct{ T }
func subject() int { var x any = Out{}; _ = x; return 1 }
`, "variable declaration boxes main.Out into any"},
	"pointer-receiver-method-set": {`package main
type T struct{ n int }
func (t *T) Set(p uintptr) { t.n = int(p) }
func subject() int { var x any = T{}; _ = x; return 1 }
`, "variable declaration boxes main.T into any"},
	"func-type-mentions": {`package main
func subject() int { var x any = func(uintptr) {}; _ = x; return 1 }
`, "variable declaration boxes func(uintptr) into any"},
	"interface-requirement-target": {`package main
type P interface{ P() uintptr }
func subject() bool { var x any = 1; _, ok := x.(P); return ok }
`, "type assertion to main.P"},
}

func TestUintptrIdentityRefusesByName(t *testing.T) {
	if n := len(uintptrRefusingShapes); n != 34 {
		t.Fatalf("the refusing table has %d entries; the records cite 34 — update the count derivation in the file header, FR-38 and BUG-124 together", n)
	}
	for name, c := range uintptrRefusingShapes {
		t.Run(name, func(t *testing.T) {
			program, err := emitSource(t, c.src)
			if err != nil {
				t.Fatalf("the per-declaration quarantine keeps the export OK: %v", err)
			}
			reason := stubReason(t, program, "subject")
			if reason == "" {
				t.Fatalf("an identity-bearing uintptr position must quarantine the declaration by name (BUG-124):\n%s", mustJSON(t, program))
			}
			for _, want := range []string{uintptrRefusalMark, c.construct, "main.go:", "release-readiness item 26", "BUG-124"} {
				if !strings.Contains(reason, want) {
					t.Errorf("the refusal must carry %q:\n%s", want, reason)
				}
			}
		})
	}
}

// stencilReason finds the ONE stencil whose wire name starts with prefix and
// mentions targ (`id[uintptr]`), and returns its quarantine reason ("" =
// lowered). Fatal if there is not exactly one.
func stencilReason(t *testing.T, program map[string]any, prefix, targ string) string {
	t.Helper()
	var found []string
	var reason string
	for name, fn := range funcNames(program) {
		if strings.HasPrefix(name, prefix) && strings.Contains(name, targ) {
			found = append(found, name)
			reason, _ = fn["unsupported"].(string)
		}
	}
	if len(found) != 1 {
		t.Fatalf("want exactly one stencil %s…%s…, got %v", prefix, targ, found)
	}
	return reason
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
	if r := stencilReason(t, program, "box", "uintptr"); !strings.Contains(r, uintptrRefusalMark) || !strings.Contains(r, "return boxes uintptr into any") {
		t.Errorf("the uintptr stencil must refuse by name, got %q", r)
	}
	if r := stencilReason(t, program, "box", "uint64"); r != "" {
		t.Errorf("the uint64 stencil must lower, got %q", r)
	}
	if r := stubReason(t, program, "subject"); r != "" {
		t.Errorf("the caller lowers (the stencil carries the refusal): %q", r)
	}
	if r := stubReason(t, program, "control"); r != "" {
		t.Errorf("the control lowers: %q", r)
	}
}

// WIDTH-ONLY generic code instantiated at uintptr LOWERS: the template's
// result tuple is substituted in the scan (fix round MEDIUM-1 — the first
// cut read `T` as an interface, a type parameter's underlying being its
// constraint, and refused `id(uintptr(7))` as «boxes uintptr into T»).
func TestUintptrIdentityGenericWidthOnlyStencilsLower(t *testing.T) {
	src := `package main
type U uintptr
func id[T any](x T) T { return x }
func maxOf[T ~uintptr | ~uint64](a, b T) T { if a > b { return a }; return b }
type B[T any] struct{ v T }
func (b B[T]) Get() T { return b.v }
func subject() int {
	p := id(uintptr(7))
	q := maxOf(uintptr(3), uintptr(9))
	r := B[uintptr]{v: 5}.Get()
	s := id(U(7))
	return int(p) + int(q) + int(r) + int(s)
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	if r := stubReason(t, program, "subject"); r != "" {
		t.Fatalf("subject must lower, got %q", r)
	}
	for _, st := range []struct{ prefix, targ string }{{"id", "uintptr"}, {"maxOf", "uintptr"}, {"id", "U"}} {
		if r := stencilReason(t, program, st.prefix, st.targ); r != "" {
			t.Errorf("the width-only stencil %s[%s] must lower, got %q", st.prefix, st.targ, r)
		}
	}
	// The method stencil B[uintptr].Get rides the methods table.
	for _, m := range program["methods"].([]any) {
		mm := m.(map[string]any)
		if rt, _ := mm["recvType"].(string); strings.Contains(rt, "uintptr") {
			if r, _ := mm["unsupported"].(string); r != "" {
				t.Errorf("the method stencil %s.Get must lower, got %q", rt, r)
			}
		}
	}
}

// The same through the loader with source-through stdlib generics:
// `slices.Max([]uintptr{…})` and `slices.Clone` are width-only.
func TestUintptrIdentityStdlibGenericsWidthOnly(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main

import "slices"

func subject() int {
	s := []uintptr{1, 9, 3}
	c := slices.Clone(s)
	return int(slices.Max(s)) + len(c)
}

func main() { println(subject()) }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	if r := stubReason(t, program, "subject"); r != "" {
		t.Fatalf("subject must lower, got %q", r)
	}
	for name, fn := range funcNames(program) {
		if r, _ := fn["unsupported"].(string); strings.Contains(r, uintptrRefusalMark) {
			t.Errorf("no declaration may carry the uintptr refusal here (width-only stdlib generics): %s: %q", name, r)
		}
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

// The BLANK package-level form `var _ any = uintptr(1)` is judged like the
// local one (fix round NIT-3): the dry run quarantines the initializer
// (effect-isolated: a constant conversion), so `$pkginit` carries no uintptr
// box — or the export refuses naming the cause. Never a silent box.
func TestUintptrIdentityBlankPackageInitializer(t *testing.T) {
	src := `package main
var _ any = uintptr(1)
func subject() int { return 1 }
`
	program, err := emitSource(t, src)
	if err != nil {
		if !strings.Contains(err.Error(), uintptrRefusalMark) {
			t.Fatalf("a whole-export refusal must name the cause: %v", err)
		}
		return
	}
	if r := stubReason(t, program, "subject"); r != "" {
		t.Errorf("subject must lower, got %q", r)
	}
	for name, fn := range funcNames(program) {
		if name == "$pkginit" && strings.Contains(mustJSON(t, fn), "uintptr") {
			t.Errorf("$pkginit must not carry the blank uintptr box:\n%s", mustJSON(t, fn))
		}
	}
}

// uintptrWidthOnlyShapes: width-only uses keep lowering — arithmetic,
// conversions, storage, pointers and slices of uintptr passed to
// NON-interface parameters, map keys of type uintptr, println, comparisons
// between uintptr values, interface values that never hold one — and NAMED
// concrete types over uintptr box and assert NOMINALLY (fix round LOW-1:
// the wire's `defined` def, the decoder's `.defined idx`; the corpus rows
// `interfaces/uintptr-identity/defined-nominal-*` pin the machine answers).
var uintptrWidthOnlyShapes = map[string]string{
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
	"blank-assign": `package main
func subject() int { _ = uintptr(1); return 1 }
`,
	// --- nominal: a NAMED concrete type over uintptr ---
	"defined-over-uintptr": `package main
type U uintptr
func subject() bool { var x any = U(1); _, ok := x.(uint64); return ok }
`,
	"defined-switch-and-equal": `package main
type U uintptr
func subject() int {
	var x any = U(1)
	n := 0
	if x == any(uint64(1)) { n += 100 }
	switch x.(type) {
	case uint64:
		n += 64
	case U:
		n += 1
	}
	return n
}
`,
	"struct-with-field": `package main
type S struct{ p uintptr }
func subject() bool { var x any = S{}; _, ok := x.(S); return ok }
`,
	"defined-error-types": `package main
type E uintptr
func (E) Error() string { return "e" }
type F uint64
func (F) Error() string { return "f" }
func subject() bool { var err error = E(1); _, ok := err.(F); return ok }
`,
	"pointer-to-defined": `package main
type U uintptr
func subject() bool { u := U(1); var x any = &u; _, ok := x.(*uint64); return ok }
`,
	// An INSTANTIATED named type is nominal too (last round LOW-1: the
	// `TypeArgs` arm dropped): `B[uintptr]` and `B[uint64]` are distinct
	// TypeIds; a collapse through a method mentioning T is the method-set
	// scan's (a method-less B here).
	"generic-nominal": `package main
type B[T any] struct{ v T }
func subject() bool { var x any = B[uintptr]{1}; _, ok := x.(B[uint64]); return ok }
`,
}

func TestUintptrIdentityWidthOnlyLowers(t *testing.T) {
	if n := len(uintptrWidthOnlyShapes); n != 18 {
		t.Fatalf("the control table has %d entries; the records cite 18 — update the count derivation in the file header, FR-38 and BUG-124 together", n)
	}
	for name, src := range uintptrWidthOnlyShapes {
		t.Run(name, func(t *testing.T) {
			program, err := emitSource(t, src)
			if err != nil {
				t.Fatalf("export must succeed: %v", err)
			}
			if r := stubReason(t, program, "subject"); r != "" {
				t.Fatalf("a width-only or nominal use of uintptr must lower, got %q", r)
			}
			if name == "generic-same-type" {
				if r := stencilReason(t, program, "id", "uintptr"); r != "" {
					t.Fatalf("the width-only stencil id[uintptr] must lower, got %q", r)
				}
			}
		})
	}
}

// A named type declared outside the source packages is judged by its
// EXPORTED method set only: `*sync.Map` (a `uintptr` hash seed inside, never
// on the wire; no uintptr in any exported method signature) is NOT this
// refusal, `*atomic.Uintptr` (`Load() uintptr`, an interface requirement
// the decoder would collapse) IS.
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
// refusal). The hook now sits after the emitter's own bodyless arm.
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
