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
//   overlay          OUR text at a library path — CAP 12; slice 1 has 0
//   primitive        machine ops of library origin — CAP 2 (print,
//                    println when G2's slice lands); slice 1 has 0
//   shim             the RETAINED user-package injections (frozen, D-002)
//   shadow-type      the E5-T shadow models (importedmodel.go)

import (
	"sort"
	"strings"
)

const (
	stdlibOverlayCap   = 12
	stdlibPrimitiveCap = 2
)

// The overlay and primitive tables are EMPTY in slice 1 by design (the
// memo's §6: "zero hand-written library text"; print/println is slice
// 3). They exist so the register's counts are derived from code, not
// asserted, and so a future entry has exactly one place to land.
var stdlibOverlays = map[string]string{}   // "<path>.<Ident>" -> reason
var stdlibPrimitives = map[string]string{} // "<builtin>" -> reason

func stdlibRegisterDump() (string, error) {
	subs, err := parseStdlibSubstitutions(stdlibSubstitutionsTSV)
	if err != nil {
		return "", err
	}
	if len(stdlibOverlays) > stdlibOverlayCap {
		return "", unsup("stdlib admission register: %d overlay functions exceed the cap of %d ([USER] re-ratification required)", len(stdlibOverlays), stdlibOverlayCap)
	}
	if len(stdlibPrimitives) > stdlibPrimitiveCap {
		return "", unsup("stdlib admission register: %d library-origin primitives exceed the cap of %d ([USER] re-ratification required)", len(stdlibPrimitives), stdlibPrimitiveCap)
	}
	var b strings.Builder
	line := func(cols ...string) { b.WriteString(strings.Join(cols, "\t") + "\n") }
	line("class", "entry", "detail")
	line("count", "source-through", itoa(len(stdlibSourceAllowed))+" (uncapped)")
	line("count", "substitution", itoa(len(subs))+" (uncapped; each names its upstream twin)")
	line("count", "overlay", itoa(len(stdlibOverlays))+" / cap "+itoa(stdlibOverlayCap))
	line("count", "primitive", itoa(len(stdlibPrimitives))+" / cap "+itoa(stdlibPrimitiveCap))
	shims := 0
	for _, fns := range stdlibShimAllowlist {
		shims += len(fns)
	}
	for _, fns := range stdlibGenericDesugarInject {
		shims += len(fns)
	}
	for _, fns := range stdlibDesugarInject {
		shims += len(fns)
	}
	for _, vars := range stdlibVarMethodInject {
		for _, methods := range vars {
			shims += len(methods)
		}
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
	for _, k := range sortedStringKeys(stdlibOverlays) {
		line("overlay", k, stdlibOverlays[k])
	}
	for _, k := range sortedStringKeys(stdlibPrimitives) {
		line("primitive", k, stdlibPrimitives[k])
	}
	shimRows := []string{}
	for path, fns := range stdlibShimAllowlist {
		for sel := range fns {
			shimRows = append(shimRows, path+"."+sel+"\tdirect-call shim (stdlibshim.go)")
		}
	}
	for path, fns := range stdlibGenericDesugarInject {
		for sel := range fns {
			shimRows = append(shimRows, path+"."+sel+"\tgeneric desugar (genericshim.go)")
		}
	}
	for path, fns := range stdlibDesugarInject {
		for sel := range fns {
			shimRows = append(shimRows, path+"."+sel+"\tfmt desugar (fmtdesugar.go)")
		}
	}
	for path, vars := range stdlibVarMethodInject {
		for v, methods := range vars {
			for m := range methods {
				shimRows = append(shimRows, path+"."+v+"."+m+"\tpackage-variable method desugar (fmtdesugar.go)")
			}
		}
	}
	sort.Strings(shimRows)
	for _, r := range shimRows {
		line("shim", r)
	}
	for _, k := range sortedStringKeys(modeledImportedTypes) {
		detail := "E5-T shadow model (importedmodel.go); source-through + overlay pending (memo §3 rows T1/T2, slice 2)"
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
