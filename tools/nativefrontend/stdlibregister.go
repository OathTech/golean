package main

// stdlibregister.go — the machine-readable half of the stdlib ADMISSION
// REGISTER (memo §2.2 "the second shim, done right", gate G8 ruled AS
// RECOMMENDED 2026-09-03 [USER, relayed]): the code's own tables, rendered
// as the TSV block docs/stdlib-admission-register.md must carry
// byte-for-byte. scripts/check-stdlib-register (a scripts/ci step)
// regenerates this dump and diffs it against the register's fenced
// block, so the register can neither rot nor be widened silently — the
// 2026-08-16 rule failed for want of exactly this check.
//
// Classes and caps (register header; the caps need a [USER]
// re-ratification to raise):
//   source-through   packages loaded from the pinned GOROOT — uncapped,
//                    each with its reason (stdlibSourceAllowed)
//   substitution     upstream-file-for-upstream-file swaps — uncapped,
//                    each naming the twin (stdlib-substitutions.tsv)
//   overlay          OUR text at a library path — CAP 12 `expr` rows
//                    (stdlib-overlay.tsv; slice 2 lands the first);
//                    `import` rows are the consequential import
//                    neutralizations, listed as `overlay-import`, not
//                    counted (see the table's header)
//   primitive        machine ops of library origin — CAP 2 (print,
//                    println when G2's slice lands); 0 so far
//   shim             the RETAINED user-package injections (frozen, D-002;
//                    since slice 2 only the fmt desugar's 6 members)
//   shadow-type      the E5-T shadow models (importedmodel.go; since
//                    slice 2 only the sync/atomic wrappers)

import (
	"sort"
	"strings"
)

const (
	stdlibOverlayCap   = 12
	stdlibPrimitiveCap = 2
	// stdlibOverlayImportCap: the consequential `import` rows' OWN cap
	// (audit fix round, [AGENT] structural decision disclosed for the
	// [USER]): 5 today + headroom for bytes' MakeNoZero import should a
	// later slice overlay those sites. The NUMBER is [AGENT]-provisional
	// pending [USER] ratification; the expr cap keeps its meaning
	// "semantic substitutions" — honest only because expr rows are barred
	// from import lines (stdlibsource.go applyStdlibOverlay, F2).
	stdlibOverlayImportCap = 8
)

// The overlay table lives in stdlib-overlay.tsv (stdlibsource.go parses
// and APPLIES it — one source for the substitutions and for the rows
// below). The primitive table is EMPTY (print/println is slice 3). Both
// exist so the register's counts are derived from code, not asserted.
var stdlibPrimitives = map[string]string{} // "<builtin>" -> reason

func stdlibRegisterDump() (string, error) {
	subs, err := parseStdlibSubstitutions(stdlibSubstitutionsTSV)
	if err != nil {
		return "", err
	}
	overlays, err := parseStdlibOverlay(stdlibOverlayTSV)
	if err != nil {
		return "", err
	}
	overlayExpr, overlayImports := stdlibOverlayCount(overlays)
	if overlayExpr > stdlibOverlayCap {
		return "", unsup("stdlib admission register: %d overlay sites exceed the cap of %d ([USER] re-ratification required)", overlayExpr, stdlibOverlayCap)
	}
	if overlayImports > stdlibOverlayImportCap {
		return "", unsup("stdlib admission register: %d overlay import-neutralization rows exceed the cap of %d ([USER] re-ratification required)", overlayImports, stdlibOverlayImportCap)
	}
	if len(stdlibPrimitives) > stdlibPrimitiveCap {
		return "", unsup("stdlib admission register: %d library-origin primitives exceed the cap of %d ([USER] re-ratification required)", len(stdlibPrimitives), stdlibPrimitiveCap)
	}
	var b strings.Builder
	line := func(cols ...string) { b.WriteString(strings.Join(cols, "\t") + "\n") }
	line("class", "entry", "detail")
	line("count", "source-through", itoa(len(stdlibSourceAllowed))+" (uncapped)")
	line("count", "substitution", itoa(len(subs))+" (uncapped; each names its upstream twin)")
	line("count", "overlay", itoa(overlayExpr)+" / cap "+itoa(stdlibOverlayCap)+" (expr sites, stdlib-overlay.tsv; byte-checked at every load)")
	line("count", "overlay-import", itoa(overlayImports)+" / cap "+itoa(stdlibOverlayImportCap)+" (consequential import neutralizations of overlaid files; no semantics; own cap, [AGENT]-provisional pending [USER])")
	intercepts := 0
	for _, ms := range frontendInterceptedLibraryMembers {
		intercepts += len(ms)
	}
	line("count", "intercept", itoa(intercepts)+" (library members whose direct call the frontend lowers to a machine op or a retained desugar instead of the library body — stdlibreach.go frontendInterceptedLibraryMembers, one predicate for reach walk and emitter)")
	line("count", "primitive", itoa(len(stdlibPrimitives))+" / cap "+itoa(stdlibPrimitiveCap))
	shims := 0
	for _, fns := range stdlibShimAllowlist {
		shims += len(fns)
	}
	for _, fns := range stdlibDesugarInject {
		shims += len(fns)
	}
	for _, fns := range stdlibGenericDesugarInject {
		shims += len(fns)
	}
	line("count", "shim", itoa(shims)+" (frozen, D-002; retired by rows of memo §3)")
	line("count", "shadow-type", itoa(len(modeledImportedTypes)))

	paths := sortedStringKeys(stdlibSourceAllowed)
	for _, p := range paths {
		line("source-through", p, stdlibSourceAllowed[p])
	}
	for _, s := range subs {
		line("substitution", s.pkg+"/"+s.drop+" -> "+s.add, s.reason)
	}
	for _, r := range overlays {
		if r.kind == "expr" {
			line("overlay", r.site(), "`"+r.old+"` -> `"+r.new+"` — "+r.reason)
		}
	}
	for _, r := range overlays {
		if r.kind == "import" {
			line("overlay-import", r.site(), "`"+r.old+"` -> `"+r.new+"` — "+r.reason)
		}
	}
	for _, k := range sortedStringKeys(stdlibPrimitives) {
		line("primitive", k, stdlibPrimitives[k])
	}
	interceptRows := []string{}
	for path, ms := range frontendInterceptedLibraryMembers {
		for m, why := range ms {
			interceptRows = append(interceptRows, path+"."+m+"\t"+why)
		}
	}
	sort.Strings(interceptRows)
	for _, r := range interceptRows {
		line("intercept", r)
	}
	shimRows := []string{}
	for path, fns := range stdlibShimAllowlist {
		for sel := range fns {
			shimRows = append(shimRows, path+"."+sel+"\tdirect-call shim (stdlibshim.go)")
		}
	}
	for path, fns := range stdlibDesugarInject {
		for sel := range fns {
			shimRows = append(shimRows, path+"."+sel+"\tfmt desugar (fmtdesugar.go; memo §2.3.3 / G5 — slice 4 re-homes it; its bundle keeps goleanShimErrorsNew as Errorf's error constructor only)")
		}
	}
	for path, fns := range stdlibGenericDesugarInject {
		for sel := range fns {
			shimRows = append(shimRows, path+"."+sel+"\tgeneric kind-dispatch desugar (cmpshim.go) — RETAINED by slice 2's STOP rule: its retirement flips slices/sortfunc-cmp/cmp-compare-kinds red on mono.go's function-local-type instantiation naming refusal; posed to the [USER] (evidence README); floats fall through to the real generic")
		}
	}
	sort.Strings(shimRows)
	for _, r := range shimRows {
		line("shim", r)
	}
	for _, k := range sortedStringKeys(modeledImportedTypes) {
		detail := "E5-T shadow model (importedmodel.go) — NOT admitted: strings.Builder/bytes.Buffer retired onto source-through + overlay in slice 2; a new non-intrinsic entry here is a register widening"
		if modeledImportedTypes[k].intrinsic {
			detail = "E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)"
		}
		line("shadow-type", k, detail)
	}
	return b.String(), nil
}

func sortedStringKeys[V any](m map[string]V) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}
