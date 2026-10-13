package main

// budgets.go — the interpreter's MATERIALIZATION BUDGETS applied PER
// DECLARATION (BUG-078; finding F2 of the 2026-10-13 fresh-eyes
// fail-closed pass, docs/2026-10-13_fresh-eyes-fail-closed-pass.md on
// branch audit/freshpass-1013, verbatim: «a decode-time budget refusal
// (`[70000]int` literal, `arrayLenBudget`) refuses the whole wire — 27
// unrelated subjects went `error`. Named and closed, but the frontend's
// per-declaration quarantine does not cover these budgets. Fix: apply
// them per declaration in the frontend.»; lane
// frontend/decl-budgets-1013 [AGENT], under [USER] Mike's 2026-10-12
// backlog mandate, relayed).
//
// TWO DOORS, ONE RULE. The decoder (GoLean/NativeToIR.lean
// `arrayLenBudget`, `arrayFootprintBudget`, `checkMakeFootprint`) keeps
// its three refusals unchanged: it is the WHOLE-WIRE BACKSTOP for a
// forged or hand-built wire and for anything this file under-estimates.
// This file is the PER-DECLARATION FRONT DOOR: the same rule, computed
// on go/types, raised as an ordinary `unsupported` at emitType / the
// make site, so the standing quarantines apply — a function or method
// becomes an H-3 stub, a package-level var is FR-24-poisoned (its
// readers stub; its initializer is H-11's to decide), a declared type
// becomes an existence-only marker TypeDef — and the rest of the
// package exports. Init code (an init() body, a non-isolated
// initializer) keeps the standing whole-export refusal (design note §2:
// init runs before every subject).
//
// THE NUMBERS are read from budgets.tsv (embedded), never spelled here;
// Tests/GoCoreEval.lean pins that table to the Lean constants.
//
// THE RULE, mirrored from the decoder:
//   - an ARRAY type `[n]E` refuses when n > arrayLenBudget (checked
//     first, as the decoder's array arm does), then when its footprint
//     n × footprint(E) > arrayFootprintBudget (innermost first);
//   - a declared STRUCT type refuses when the SUM of its fields'
//     footprints exceeds arrayFootprintBudget (the decoder's TypeDef
//     check);
//   - the FOOTPRINT (`tyFootprint?` / `typeDefFootprint?`): an array is
//     its length times its element's; a source-declared named type is
//     its underlying's; a struct is the sum of its fields, at least 1;
//     everything else — scalars, pointers, slices, maps, channels,
//     funcs, interfaces, sync primitives, and IMPORTED named types (D5
//     markers are one leaf in the decoder; an E5-T shadow model's
//     TypeDef is the model's, not go/types' — counted as one leaf here,
//     an UNDER-estimate the decoder's backstop still catches whole-wire)
//     — is one leaf;
//   - a `make([]E, len[, cap])` with a CONSTANT count n (the cap when a
//     cap operand is spelled, else the len; read off the EMITTED wire
//     operand exactly as the decoder's `unseqConstInt?` reads it)
//     refuses when n × footprint(E) > arrayFootprintBudget — but ONLY
//     behind the make site's own order: gc's makeslice panic first
//     (n × Sizeof(E) > maxAllocBytes, gc/amd64 sizes), then the
//     machine's count bound (n > sliceCapBudget); both stay Go-
//     observable / the machine's own refusal, never pre-empted here.
//
// A NAMED type is refused at every mention outside SIGNATURE-OPAQUE mode
// when it REACHES a violation — through arrays, struct fields, pointers,
// slices, maps, channels, func signatures and other source-declared
// named types (not through interfaces: their requirement lists are
// emitted in signature-opaque mode). Its own TypeDef is then the marker,
// so the decoder never sees the over-budget shape and no body can hold a
// value of it; in signature-opaque mode (quarantined method stubs,
// interface requirement lists) the reference names the marker so
// satisfaction still answers. An inline over-budget ARRAY in a signature
// gets the FR-25-shaped opaque marker under its own spelling.

import (
	_ "embed"
	"fmt"
	"go/types"
	"math"
	"strconv"
	"strings"
)

//go:embed budgets.tsv
var budgetsTSV string

// materializationBudgets: the four numbers of budgets.tsv.
type materializationBudgets struct {
	arrayLen       int64
	arrayFootprint int64
	sliceCap       int64
	maxAllocBytes  int64
}

// budgets is parsed once at start-up; a malformed table PANICS (the
// frontend cannot apply an unknown bound — fail closed, loudly).
var budgets = mustParseBudgets(budgetsTSV)

func mustParseBudgets(src string) materializationBudgets {
	b, err := parseBudgets(src)
	if err != nil {
		panic("tools/nativefrontend/budgets.tsv: " + err.Error())
	}
	return b
}

func parseBudgets(src string) (materializationBudgets, error) {
	want := map[string]*int64{}
	var b materializationBudgets
	want["arrayLenBudget"] = &b.arrayLen
	want["arrayFootprintBudget"] = &b.arrayFootprint
	want["sliceCapBudget"] = &b.sliceCap
	want["maxAllocBytes"] = &b.maxAllocBytes
	seen := map[string]bool{}
	header := false
	for i, line := range strings.Split(src, "\n") {
		if strings.HasPrefix(line, "#") || strings.TrimSpace(line) == "" {
			continue
		}
		f := strings.Split(line, "\t")
		if !header {
			if line != "name\tvalue\tlean" {
				return b, fmt.Errorf("line %d: header is %q, want name/value/lean", i+1, line)
			}
			header = true
			continue
		}
		if len(f) != 3 {
			return b, fmt.Errorf("line %d: %d column(s), want 3", i+1, len(f))
		}
		dst, known := want[f[0]]
		if !known {
			return b, fmt.Errorf("line %d: unknown budget %q", i+1, f[0])
		}
		if seen[f[0]] {
			return b, fmt.Errorf("line %d: duplicate budget %q", i+1, f[0])
		}
		v, err := strconv.ParseInt(f[1], 10, 64)
		if err != nil || v <= 0 {
			return b, fmt.Errorf("line %d: budget %s value %q is not a positive decimal int64", i+1, f[0], f[1])
		}
		*dst = v
		seen[f[0]] = true
	}
	if !header {
		return b, fmt.Errorf("no header line")
	}
	for name := range want {
		if !seen[name] {
			return b, fmt.Errorf("budget %s missing", name)
		}
	}
	return b, nil
}

// satMul: a × b saturating at MaxInt64 (both non-negative). Every
// comparison is against a budget far below the saturation point, so a
// saturated product is still correctly "over".
func satMul(a, b int64) int64 {
	if a == 0 || b == 0 {
		return 0
	}
	if a > math.MaxInt64/b {
		return math.MaxInt64
	}
	return a * b
}

func satAdd(a, b int64) int64 {
	if a > math.MaxInt64-b {
		return math.MaxInt64
	}
	return a + b
}

// gcSizes: gc's layout at the pinned target (linux/amd64) — the sizes
// gc's own makeslice check multiplies (the machine's `tySizeBytes`
// is cross-checked against gc, docs/evidence/2026-10-07_field-offsets/).
var gcSizes = types.SizesFor("gc", "amd64")

// budgetLeafNamed: a named type that is one LEAF for the footprint and
// carries no budget violation of its own here — interfaces, the sync
// primitives, and every named type declared outside the source program
// (D5 markers / E5-T shadow models; see the file comment).
func (e *emitter) budgetLeafNamed(n *types.Named) bool {
	if _, iface := n.Underlying().(*types.Interface); iface {
		return true
	}
	obj := n.Obj()
	if obj.Pkg() == nil {
		return true
	}
	if !e.isSourcePackage(obj.Pkg()) {
		return true
	}
	if e.isLibraryPackage(obj.Pkg()) && modeledImportedTypes[e.qualifiedTypeNameNoNote(obj)] != nil {
		return true
	}
	return false
}

// qualifiedTypeNameNoNote: the package-qualified name WITHOUT registering
// a display (qualifiedTypeName notes one; the budget walk must have no
// side effects). Only used for the modeled-type lookup.
func (e *emitter) qualifiedTypeNameNoNote(obj *types.TypeName) string {
	if obj.Pkg() == nil {
		return obj.Name()
	}
	return obj.Pkg().Path() + "." + obj.Name()
}

// budgetFootprint: the decoder's FOOTPRINT of t in scalar leaves
// (`tyFootprint?` + `typeDefFootprint?`), saturating.
func (e *emitter) budgetFootprint(t types.Type) int64 {
	return e.budgetFootprintDepth(t, 0)
}

func (e *emitter) budgetFootprintDepth(t types.Type, depth int) int64 {
	if depth > 64 {
		// Go forbids value-recursive types (go/types refuses them), so
		// this depth is unreachable on a type-checked program; saturate
		// (over-budget) rather than guess.
		return math.MaxInt64
	}
	switch u := types.Unalias(t).(type) {
	case *types.Array:
		return satMul(u.Len(), e.budgetFootprintDepth(u.Elem(), depth+1))
	case *types.Named:
		if e.budgetLeafNamed(u) {
			return 1
		}
		return e.budgetFootprintDepth(u.Underlying(), depth+1)
	case *types.Struct:
		var total int64
		for i := 0; i < u.NumFields(); i++ {
			total = satAdd(total, e.budgetFootprintDepth(u.Field(i).Type(), depth+1))
		}
		if total < 1 {
			total = 1
		}
		return total
	default:
		return 1
	}
}

// arrayBudgetViolation: the decoder's array-arm rule on ONE array type
// (its element already checked by the caller's recursion): the
// per-dimension bound first, then the nested footprint. "" = admitted.
func (e *emitter) arrayBudgetViolation(a *types.Array) string {
	spelled := types.TypeString(a, nil)
	if a.Len() > budgets.arrayLen {
		return fmt.Sprintf("materialization budget (BUG-078): array type %s of %d elements exceeds the per-dimension budget %d (arrayLenBudget, tools/nativefrontend/budgets.tsv)",
			spelled, a.Len(), budgets.arrayLen)
	}
	if fp := e.budgetFootprint(a); fp > budgets.arrayFootprint {
		return fmt.Sprintf("materialization budget (BUG-078): array type %s of %d scalar elements through its nesting exceeds the nested budget %d (arrayFootprintBudget, tools/nativefrontend/budgets.tsv)",
			spelled, fp, budgets.arrayFootprint)
	}
	return ""
}

// typeBudgetViolation: the first budget violation t REACHES (file
// comment: through arrays, struct fields, pointers, slices, maps,
// channels, signatures and source-declared named types; never through
// interfaces or imported named types). "" = none. Pure; a named type's
// answer is memoized only when it is COMPLETE — a walk that cut a
// recursion at a named type still open further up the stack (`A{ b *B;
// x [70000]int }` reaches B before A's own field) does not memoize the
// inner type (B), whose answer depends on the outer one's (A).
func (e *emitter) typeBudgetViolation(t types.Type) string {
	if e.budgetMemo == nil {
		e.budgetMemo = map[*types.Named]string{}
	}
	v, _ := e.typeBudgetViolationWalk(t, map[*types.Named]int{}, 0)
	return v
}

// typeBudgetViolationWalk returns the violation and the LOWEST stack
// index of an open named type whose recursion it cut (noCut if none).
const noCut = math.MaxInt

func (e *emitter) typeBudgetViolationWalk(t types.Type, visiting map[*types.Named]int, depth int) (string, int) {
	if t == nil || depth > 64 {
		return "", noCut
	}
	// seq: walk a list of component types, first violation wins; the cut
	// mark is the minimum over the components walked.
	seq := func(ts ...types.Type) (string, int) {
		low := noCut
		for _, c := range ts {
			v, cut := e.typeBudgetViolationWalk(c, visiting, depth+1)
			if cut < low {
				low = cut
			}
			if v != "" {
				return v, low
			}
		}
		return "", low
	}
	switch u := types.Unalias(t).(type) {
	case *types.Array:
		if u.Len() > budgets.arrayLen {
			return e.arrayBudgetViolation(u), noCut
		}
		v, cut := seq(u.Elem())
		if v != "" {
			return v, cut
		}
		return e.arrayBudgetViolation(u), cut
	case *types.Named:
		if e.budgetLeafNamed(u) {
			return "", noCut
		}
		if v, done := e.budgetMemo[u]; done {
			return v, noCut
		}
		if idx, open := visiting[u]; open {
			return "", idx // recursion through a pointer/slice/map/chan/func
		}
		idx := len(visiting)
		visiting[u] = idx
		v, low := seq(u.Underlying())
		if v == "" {
			if st, isStruct := u.Underlying().(*types.Struct); isStruct {
				if fp := e.budgetFootprint(st); fp > budgets.arrayFootprint {
					v = fmt.Sprintf("materialization budget (BUG-078): type %s of %d scalar elements across its fields and nesting exceeds the nested budget %d (arrayFootprintBudget, tools/nativefrontend/budgets.tsv)",
						u.Obj().Name(), fp, budgets.arrayFootprint)
				}
			}
		} else if !strings.HasPrefix(v, "type "+u.Obj().Name()+" ") {
			v = "type " + u.Obj().Name() + " reaches " + v
		}
		delete(visiting, u)
		if low >= idx {
			// Every cut this walk made was at u itself (now closed) or
			// none: the answer is complete.
			e.budgetMemo[u] = v
			low = noCut
		}
		return v, low
	case *types.Struct:
		fs := make([]types.Type, u.NumFields())
		for i := range fs {
			fs[i] = u.Field(i).Type()
		}
		return seq(fs...)
	case *types.Pointer:
		return seq(u.Elem())
	case *types.Slice:
		return seq(u.Elem())
	case *types.Chan:
		return seq(u.Elem())
	case *types.Map:
		return seq(u.Key(), u.Elem())
	case *types.Signature:
		var ts []types.Type
		for _, tup := range []*types.Tuple{u.Params(), u.Results()} {
			for i := 0; i < tup.Len(); i++ {
				ts = append(ts, tup.At(i).Type())
			}
		}
		return seq(ts...)
	default:
		return "", noCut
	}
}

// opaqueBudgetArrayRef: in SIGNATURE-OPAQUE mode an over-budget inline
// array type emits as an opaque `named` marker under its own spelling
// (the FR-25 shape: `[70000]int` cannot collide with a declared TypeId,
// which is package-qualified and bracket-free at its head), recorded for
// an existence-only TypeDef (budgetMarkerTypeDefs). Array identity is
// structural, and both sides of a satisfaction question — the
// requirement list and the stub — are emitted in this mode, so identical
// keys ⇔ identical Go types; no value of the type ever exists.
func (e *emitter) opaqueBudgetArrayRef(a *types.Array, reason string) map[string]any {
	key := types.TypeString(a, nil)
	if e.opaqueBudgetArrays == nil {
		e.opaqueBudgetArrays = map[string]string{}
	}
	e.opaqueBudgetArrays[key] = reason
	e.noteTypeDisplay(key, typeDisplay{display: key})
	return map[string]any{"kind": "named", "name": key}
}

// budgetMarkerTypeDefs: the existence-only TypeDefs of the opaque
// budget-array markers (sorted, deterministic).
func (e *emitter) budgetMarkerTypeDefs() []any {
	out := []any{}
	for _, key := range sortedStringKeys(e.opaqueBudgetArrays) {
		out = append(out, map[string]any{
			"name": key,
			"def": map[string]any{"kind": "unsupported",
				"feature": e.opaqueBudgetArrays[key] +
					" — carried as an opaque marker in declaration signatures only; no value of it ever lowers; satisfaction answers, every structural use refuses"},
		})
	}
	return out
}

// wireConstInt: the decoder's `unseqConstInt?` on an EMITTED operand —
// a literal `{"expr":"int","value":"<decimal>"}` node; anything else is
// not a constant count for the make bound (ok = false).
func wireConstInt(j any) (int64, bool) {
	m, isMap := j.(map[string]any)
	if !isMap {
		return 0, false
	}
	if m["expr"] != "int" {
		return 0, false
	}
	s, isStr := m["value"].(string)
	if !isStr {
		return 0, false
	}
	v, err := strconv.ParseInt(s, 10, 64)
	if err != nil {
		// Larger than int64: far past every bound; gc rejects such a
		// constant count at compile time (not representable as int).
		return 0, false
	}
	return v, true
}

// makeBudgetViolation: the decoder's `checkMakeFootprint`, PRECEDENCE
// INCLUDED, on the emitted operands of `make([]elem, lenJ[, capJ])`
// (capJ nil when no cap operand is spelled). "" = admitted or not this
// check's (a run-time count; gc's panic; the machine's count refusal).
func (e *emitter) makeBudgetViolation(elem types.Type, lenJ, capJ any) string {
	var n int64
	var ok bool
	if capJ != nil {
		n, ok = wireConstInt(capJ)
	} else {
		n, ok = wireConstInt(lenJ)
	}
	if !ok || n <= 0 {
		return ""
	}
	// (i) gc's own makeslice panic — Go-observable, the machine's.
	if satMul(n, gcSizes.Sizeof(elem)) > budgets.maxAllocBytes {
		return ""
	}
	// (ii) the machine's count bound — its own named refusal.
	if n > budgets.sliceCap {
		return ""
	}
	// (iii) only then the footprint.
	f := e.budgetFootprint(elem)
	if satMul(n, f) > budgets.arrayFootprint {
		return fmt.Sprintf("materialization budget (BUG-078): make([]%s, %d) materializes %d scalar elements (%d × %d per element), past the footprint budget for a constant-length make %d (arrayFootprintBudget, tools/nativefrontend/budgets.tsv)",
			types.TypeString(elem, nil), n, satMul(n, f), n, f, budgets.arrayFootprint)
	}
	return ""
}
