package main

// Unit tests for the two whole-export kills turned per-declaration on
// 2026-09-04 (ledger FR-22 / FR-23; cedar-go census 2026-09-03 §3.2-3.3).
// The differential corpus pins the OBSERVABLE contract (init/stdlib-
// initializer-*, generics/imported-generic-*); these pin what the
// differential structurally cannot see:
//
//   FR-23  the opaque marker is minted ONLY in signature position, the
//          stub carries the real signature under the mangled key, the
//          marker TypeDef exists, the interface requirement mints the
//          SAME key (satisfaction identity), a body use still refuses,
//          and the flag is never left on;
//   FR-22  a register-row callee poisons per declaration with the cell
//          re-typed `$poisoned` (seedable) and the reader named; an
//          unregistered callee still refuses the WHOLE export naming the
//          register; the argument-shape holes (nil Location, a
//          source-declared pointer) refuse; the register dump renders
//          the class.

import (
	"strings"
	"testing"
)

func typeDefByName(program map[string]any, name string) map[string]any {
	tds, _ := program["types"].([]any)
	for _, td := range tds {
		m, ok := td.(map[string]any)
		if ok && m["name"] == name {
			return m
		}
	}
	return nil
}

func funcByName(program map[string]any, name string) map[string]any {
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		m, ok := f.(map[string]any)
		if ok && m["name"] == name {
			return m
		}
	}
	return nil
}

func globalByName(program map[string]any, name string) map[string]any {
	gs, _ := program["globals"].([]any)
	for _, g := range gs {
		m, ok := g.(map[string]any)
		if ok && m["name"] == name {
			return m
		}
	}
	return nil
}

func namedTypeName(t any) string {
	m, ok := t.(map[string]any)
	if !ok || m["kind"] != "named" {
		return ""
	}
	n, _ := m["name"].(string)
	return n
}

const opaqueSigSrc = `package main

import "iter"

type Bag struct{ items []int }

func (b Bag) All() iter.Seq[int] {
	return func(yield func(int) bool) {
		for _, v := range b.items {
			if !yield(v) {
				return
			}
		}
	}
}

func (b Bag) Sum(s iter.Seq[int]) int {
	t := 0
	for v := range s {
		t += v
	}
	return t
}

type Iterable interface{ All() iter.Seq[int] }

type Outer struct{ Bag }

func consume() int {
	n := 0
	for v := range (Bag{items: []int{1}}).All() {
		n += v
	}
	return n
}

func main() { println(consume()) }
`

func TestOpaqueSignatureStubKeepsExport(t *testing.T) {
	program, err := emitSource(t, opaqueSigSrc)
	if err != nil {
		t.Fatalf("imported generic in a method SIGNATURE must stub per declaration, not refuse the export (FR-23): %v", err)
	}
	all := findMethod(program, "main.Bag", "All")
	if all == nil {
		t.Fatalf("Bag.All dropped from the method table (D2 completeness)")
	}
	reason, _ := all["unsupported"].(string)
	if !strings.Contains(reason, "iter.Seq[int]") || !strings.Contains(reason, "FR-23") {
		t.Fatalf("stub refusal does not name the opaque instantiation and FR-23: %q", reason)
	}
	results, _ := all["results"].([]any)
	if len(results) != 1 {
		t.Fatalf("stub carries %d results, want 1 (the real signature)", len(results))
	}
	r0, _ := results[0].(map[string]any)
	if got := namedTypeName(r0["type"]); got != "iter.Seq[int]" {
		t.Fatalf("stub result type = %v, want opaque named iter.Seq[int]", r0["type"])
	}
	td := typeDefByName(program, "iter.Seq[int]")
	if td == nil {
		t.Fatalf("no marker TypeDef for the opaque instantiation")
	}
	def, _ := td["def"].(map[string]any)
	if def["kind"] != "unsupported" {
		t.Fatalf("marker TypeDef kind = %v, want unsupported (the D5 shape)", def["kind"])
	}
	// Param position too.
	sum := findMethod(program, "main.Bag", "Sum")
	if sum == nil || sum["unsupported"] == nil {
		t.Fatalf("Bag.Sum (opaque in PARAM position) must be a stub: %v", sum)
	}
}

func TestOpaqueInterfaceRequirementMintsSameKey(t *testing.T) {
	program, err := emitSource(t, opaqueSigSrc)
	if err != nil {
		t.Fatalf("export: %v", err)
	}
	td := typeDefByName(program, "main.Iterable")
	if td == nil {
		t.Fatalf("interface Iterable has no TypeDef")
	}
	def, _ := td["def"].(map[string]any)
	methods, _ := def["methods"].([]any)
	if len(methods) != 1 {
		t.Fatalf("Iterable requirement list has %d methods, want 1", len(methods))
	}
	m0, _ := methods[0].(map[string]any)
	results, _ := m0["results"].([]any)
	if len(results) != 1 || namedTypeName(results[0]) != "iter.Seq[int]" {
		t.Fatalf("Iterable.All requirement result = %v, want the SAME opaque key iter.Seq[int] the stub carries (satisfaction identity)", results)
	}
	// The promoted All on Outer is a stub too (the wrapper cannot type
	// its forwarding body), never dropped.
	prom := findMethod(program, "main.Outer", "All")
	if prom == nil {
		t.Fatalf("promoted Outer.All dropped (D2: satisfaction would answer a false no)")
	}
	if r, _ := prom["unsupported"].(string); !strings.Contains(r, "promoted method") || !strings.Contains(r, "iter.Seq[int]") {
		t.Fatalf("promoted stub reason does not name the cause: %q", r)
	}
}

func TestOpaqueNeverAdmittedInBody(t *testing.T) {
	program, err := emitSource(t, opaqueSigSrc)
	if err != nil {
		t.Fatalf("export: %v", err)
	}
	c := funcByName(program, "consume")
	if c == nil {
		t.Fatalf("consume missing")
	}
	r, _ := c["unsupported"].(string)
	if !strings.Contains(r, "instantiation of imported generic type iter.Seq[int]") {
		t.Fatalf("a BODY that consumes the opaque type must quarantine by name, got: %v", c)
	}
	// One more time through the raw emitter: the flag must be off after
	// every signature pass (a leak would admit the type in bodies).
	e := &emitter{}
	if _, err := e.withOpaqueSigs(func() error { return nil }); err != nil || e.sigOpaque {
		t.Fatalf("withOpaqueSigs left sigOpaque=%v", e.sigOpaque)
	}
}

const poisonSrc = `package main

import "time"

var seq []string

func note(s string) int { seq = append(seq, s); return len(seq) }

var a = note("a")
var maxDatetime = time.Date(292278994, 8, 17, 7, 12, 55, 807*1e6, time.UTC)
var b = note("b")
var alias = maxDatetime

func reader() bool { return maxDatetime.IsZero() }
func cascade() bool { return alias.IsZero() }
func sibling() int  { return a + b }

func main() { println(sibling(), reader(), cascade()) }
`

func TestRegisterRowCalleePoisonsPerDeclaration(t *testing.T) {
	program, err := emitSource(t, poisonSrc)
	if err != nil {
		t.Fatalf("time.Date is an init-callee register row: its initializer must poison, not refuse the export (FR-22): %v", err)
	}
	if n := pkginitStmtCount(t, program); n != 2 {
		t.Fatalf("$pkginit carries %d statements, want 2 (a, b — seq has no initializer; the poisoned two skipped)", n)
	}
	for _, name := range []string{"maxDatetime", "alias"} {
		g := globalByName(program, name)
		if g == nil {
			t.Fatalf("poisoned var %s dropped from the globals table (gid density)", name)
		}
		if got := namedTypeName(g["type"]); got != poisonedCellTypeId {
			t.Fatalf("poisoned var %s seeds as %v, want named %s (a time.Time cell has no default value; seeding would refuse EVERY subject)", name, g["type"], poisonedCellTypeId)
		}
	}
	if g := globalByName(program, "a"); g == nil || namedTypeName(g["type"]) == poisonedCellTypeId {
		t.Fatalf("healthy var a was re-typed: %v", g)
	}
	td := typeDefByName(program, poisonedCellTypeId)
	if td == nil {
		t.Fatalf("no %s TypeDef", poisonedCellTypeId)
	}
	for _, fn := range []string{"reader", "cascade"} {
		f := funcByName(program, fn)
		r, _ := f["unsupported"].(string)
		if !strings.Contains(r, "package-level var") || !strings.Contains(r, "time.Date") {
			t.Fatalf("%s must be a stub naming the var and the callee, got %v", fn, f)
		}
	}
	if f := funcByName(program, "sibling"); f == nil || f["unsupported"] != nil {
		t.Fatalf("sibling must lower: %v", f)
	}
}

func TestUnregisteredCalleeStillRefusesWholeExport(t *testing.T) {
	const src = `package main

import "os"

var pid = os.Getpid()

func unrelated() int { return 7 }

func main() { println(unrelated()) }
`
	_, err := emitSource(t, src)
	if err == nil {
		t.Fatalf("os.Getpid is NOT an init-callee register row: the export must refuse (skipping cannot be argued unobservable)")
	}
	msg := err.Error()
	for _, want := range []string{"pid", "os.Getpid", "init-callee register", "FR-22"} {
		if !strings.Contains(msg, want) {
			t.Fatalf("whole-export refusal must name %q: %s", want, msg)
		}
	}
}

func TestRegisterRowArgumentShapeHoles(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"nil location (Date panics)", `package main

import "time"

var d = time.Date(2020, 1, 1, 0, 0, 0, 0, nil)

func main() {}
`, "d"},
		{"source-declared pointer arg", `package main

import "time"

var loc *time.Location

var d = time.Date(2020, 1, 1, 0, 0, 0, 0, loc)

func main() {}
`, "d"},
		{"dependent method call (not isolated)", `package main

import "time"

var d = time.Date(2020, 1, 1, 0, 0, 0, 0, time.UTC)
var y = d.Year()

func main() {}
`, "y"},
	}
	for _, tc := range cases {
		_, err := emitSource(t, tc.src)
		if err == nil {
			t.Fatalf("%s: was ADMITTED — a skipped panicking/aliasing initializer is a silent wrong answer", tc.name)
		}
		if !strings.Contains(err.Error(), "initializer of "+tc.want) {
			t.Fatalf("%s: refusal does not name the declaration %q: %v", tc.name, tc.want, err)
		}
	}
}

func TestRegisterDumpRendersInitCalleeClass(t *testing.T) {
	dump, err := stdlibRegisterDump()
	if err != nil {
		t.Fatalf("register dump: %v", err)
	}
	if !strings.Contains(dump, "count\tinit-callee\t"+itoa(len(pureUnmodeledCallees))) {
		t.Fatalf("register dump lacks the init-callee count line")
	}
	for k, why := range pureUnmodeledCallees {
		if !strings.Contains(dump, "init-callee\t"+k+"\t"+why) {
			t.Fatalf("register dump lacks the row for %s", k)
		}
		if why == "" {
			t.Fatalf("row %s has no written argument", k)
		}
	}
}

// The opaque marker carries no method stubs, so an imported generic
// instantiation WITH exported methods must REFUSE in signature position
// (a stub-less marker would let satisfaction answer a false no — the D5
// skip-whole hazard; audit fix round item 7). unique.Handle[T] has Value().
func TestOpaqueRefusesImportedGenericWithMethods(t *testing.T) {
	const src = `package main

import "unique"

type Bag struct{ items []int }

func (b Bag) H() unique.Handle[int] { return unique.Make(1) }

func main() {}
`
	_, err := emitSource(t, src)
	if err == nil {
		t.Fatalf("an imported generic WITH methods in a signature must refuse, not get a stub-less marker")
	}
	if !strings.Contains(err.Error(), "unique.Handle[int]") || !strings.Contains(err.Error(), "Value") {
		t.Fatalf("refusal must name the type and its exported method(s): %v", err)
	}
}
