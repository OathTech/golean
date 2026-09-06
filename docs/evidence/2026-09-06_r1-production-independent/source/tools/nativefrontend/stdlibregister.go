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
//   primitive        machine ops of library origin — CAP 2, FULL since
//                    stdlib slice 3 (2026-09-04): `float-bits` (math's
//                    four bit-reinterpretation functions, [USER]-admitted)
//                    and `print-output` (print/println + the fd-2 output
//                    observable, gate G2). Widening past 2 is a [USER]
//                    re-ratification (an over-cap table refuses to render).
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
// below). The primitive table names the two library-origin machine ops
// (stdlib slice 3). Both exist so the register's counts are derived from
// code, not asserted.
var stdlibPrimitives = map[string]string{
	"float-bits":   "math.Float64bits / Float64frombits / Float32bits / Float32frombits as ONE machine expression op with a direction/width tag (wire `float-bits`, GoCore `Expr.floatBits`/`floatBitsApply`; frontend floatbits.go): a bit reinterpretation the LANGUAGE has no operation for (math's bodies are `*(*uint64)(unsafe.Pointer(&f))`) over a representation that IS the bit pattern — identity both ways, NaN payloads (quiet and signalling), signed zero and the infinities BIT-EXACT (the audit's admission condition; rows builtins/float-bits/*). ADMITTED [USER] 2026-09-04 (relayed: «add this as a primitive language operation? This sounds reasonable, do it»). Anchor: deps/go/src/math/unsafe.go:21-41 @ go1.26.5 (the four doc comments — Float32bits :21-24, Float32frombits :26-30, Float64bits :32-35, Float64frombits :37-41; a file:line citation because math is NOT source-through and the pinned-manifest godoc: grammar of gate G3 covers source-through packages only — the runtime-source rows' convention). ONE fail-closed arm, [AGENT] disclosed: `*bits` of the machine's CANONICAL NaN (0x7FF8000000000000 / 0x7FC00000) refuses by name — inventory R7 narrows every machine-PRODUCED NaN to that pattern while gc/amd64 realizes hardware payloads, so the observation would be the narrowing presenting as a wrong answer (row builtins/float-bits/canonical-nan-refused; R7's re-envelope obligation). Unblocks internal/strconv's deps.go casts for a later slice.",
	"print-output": "print / println (spec#Bootstrapping: «formatting of arguments is implementation-specific») as the `print` machine STATEMENT (wire `print`, GoCore `Stmt.print`/`StmtOp.print`/`renderPrint`; frontend emitPrintStmt) with gc's runtime/print.go @ go1.26.5 format PINNED for bool (`true`/`false`), every integer kind (decimal, `-` for negatives; a defined type prints as its underlying kind) and string (bytes verbatim); println = operands joined by ` ` + `\n`, print = concatenation. The bytes are the machine's OUTPUT EVENT (`StepEvent.out`, pool layer; folded by the driver into `Readout.output` — design gate G-OUT RULED [USER]), the differential's new `output` observation field, byte-compared against gc's fd 2 (the harness's stderr split). G2 RULED [USER] 2026-09-03 as recommended (relayed). REFUSED by name, permanently: pointer/chan/map/func/slice/interface/unsafe.Pointer operands (gc prints ADDRESSES — ledger §5.1 item 3). REFUSED by name THIS SLICE ([AGENT], disclosed): float/complex operands (gc: internal/strconv.AppendFloat 'g' -1, the shortest-repr algorithm, go1.26 commit 9035f7ae) and the zero-operand spellings (no nullary plan, A8) — ledger FR-29; print during $pkginit (the sequential init driver has no event fold — runInitConfig refuses). Latitude inventory R17 (format pin) / R18 (concurrent-print interleaving = L1, membership lane).",
}

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
	line("count", "init-callee", itoa(len(pureUnmodeledCallees))+" (H-11 pureUnmodeledCallees: unmodeled stdlib functions a package-level initializer may call and still be SKIPPED with its vars poisoned; each row states result-only + panic-free over the admitted argument shapes; a row is an admission, not a model)")

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
			shimRows = append(shimRows, path+"."+sel+"\tgeneric emit-time desugar (stdlibGenericDesugarInject — EMPTY since the cmp.Compare kind desugar retired 2026-09-04; a new entry is a register widening)")
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
	for _, k := range sortedStringKeys(pureUnmodeledCallees) {
		line("init-callee", k, pureUnmodeledCallees[k])
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
