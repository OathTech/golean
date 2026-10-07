package main

// FR-36 (2026-10-06, lane `lane/fr36-spin-bounds-1006`; [USER] Mike
// 2026-10-06 «Yeah, let's do 3+4», relayed by the [AGENT] coordinator — cite
// as relayed): a DOT import of a stdlib package (`import . "math/rand"`;
// `Intn(5)`) puts the package's members in the FILE block, so a call of one
// is a bare IDENTIFIER, not a `pkg.Member` selector. Every stdlib binding
// used to key on the SELECTOR (`emitCallNode`'s `sel.Sel`), so the bare
// identifier fell through to the user-call path: `call "Intn"` on the wire
// (frontend EXPORT OK) and `stuck: GoCore function not found: Intn` from the
// machine — fail-noisy, but a refusal that did not NAME its cause at the
// point of failure (ledger row FR-36; the 5b audit's F3,
// docs/2026-10-01_intn-pick-audit.md). The one exception was the float-bits
// family, which the audit fix round D (2026-09-05) made refuse by name as a
// stopgap while the class stayed unfixed.
//
// THE FIX: one OBJECT-keyed lookup on the resolved `*types.Func`, shared by
// the selector spelling and the bare-identifier spelling, so an import form
// can never reach a lowering the other form does not:
//   - the PRIMITIVES (`atomic-op`, `float-bits`, `rand-intn`) lower the same
//     node from either spelling (`emitPrimitiveCall`) — the op is a fact
//     about the callee object, not about how the file spelled it (the
//     lowering-diagnosis calibration, tools/lowerdiag testdata/calib/dot.go
//     `fbDot`, pins the dot-imported float-bits call SUPPLIED since
//     2026-10-06; its `dot-import-float-bits` cause is retired);
//   - a SOURCE-THROUGH member (`import . "strings"`; `ToUpper`) was already a
//     source function (`funcWireName` qualifies it) and stays green;
//   - every other non-source stdlib member refuses BY NAME with the selector
//     spelling's own text, the import form named (`refuseDotImportedCall`);
//     a fmt desugar member refuses naming the desugar (its shim injection
//     and Formatter checks are syntactic on the selector — a lowering there
//     would need two more passes taught the dot form; an honest residual);
//   - in VALUE position (`f := Intn`, `defer Intn(5)`'s callee) the qualified
//     spelling's FR-14 refusal applies, import form named
//     (`refuseDotImportedValue`): the primitives lower at direct-call sites
//     only.
// Why the bare identifier can only be a dot import: Go's universe scope
// holds builtins (`*types.Builtin`), never functions, and the loader refuses
// dot imports of SOURCE (case-local) packages (load.go, identity note §6) —
// so a `*types.Func` of another, non-source package reached as an identifier
// is exactly a dot-imported stdlib member. Rows: stdlib-source/dot-import/*.

import (
	"go/ast"
	"go/types"
)

// emitPrimitiveCall: the OBJECT-keyed primitive bindings — sync/atomic's
// package-level functions (atomics.go), the math float-bits family
// (floatbits.go) and the math/rand Intn/IntN draw (randintn.go) — shared by
// the selector and the bare-identifier spellings. handled=false means the
// callee is none of them and the caller continues down its own chain;
// handled=true returns the hook's own (node, effectful, err) verbatim.
func (e *emitter) emitPrimitiveCall(c *ast.CallExpr, obj types.Object) (node any, effectful bool, handled bool, err error) {
	if fn, isAtomic := isAtomicFunc(obj); isAtomic {
		node, effectful, err = e.emitAtomicCall(c, fn)
		return node, effectful, true, err
	}
	if fn, isFB := isFloatBitsFunc(obj); isFB {
		node, effectful, err = e.emitFloatBitsCall(c, fn)
		return node, effectful, true, err
	}
	if fn, tag, isRI := isRandIntnFunc(obj); isRI {
		node, effectful, err = e.emitRandIntnCall(c, fn, tag)
		return node, effectful, true, err
	}
	return nil, false, false, nil
}

// dotImportedStdlibFunc reports whether fn — reached as a bare IDENTIFIER —
// belongs to a package other than the current one that is NOT a source
// package (main, a case-local import, or a source-through stdlib library
// unit): exactly a dot-imported member of the quarantined / primitive-bound
// stdlib surface (header). Returns that package.
func (e *emitter) dotImportedStdlibFunc(fn *types.Func) (*types.Package, bool) {
	pkg := fn.Pkg()
	if pkg == nil || pkg == e.pkg || e.isSourcePackage(pkg) {
		return nil, false
	}
	return pkg, true
}

// refuseDotImportedCall: the dot-imported bare-identifier CALL of a
// non-source stdlib function no primitive binds. The fmt desugar members
// refuse naming the desugar (header); everything else gets the selector
// spelling's by-name package quarantine text (`emitCallNode`'s
// package-selector arm, FR-14) with the import form named, so triage groups
// the two spellings by cause.
func (e *emitter) refuseDotImportedCall(fn *types.Func, pkg *types.Package) error {
	if pkg.Path() == "fmt" && fmtDesugarFuncs[fn.Name()] {
		return unsup("dot-imported fmt.%s called as a bare identifier (import . \"fmt\"): the fmt desugar lowers the qualified spelling only — its shim injection and Formatter checks key on the selector (fmtdesugar.go, stdlibshim.go) — refused by name (FR-36 residual)", fn.Name())
	}
	return unsup("package-selector call %s.%s (package %q surface not modeled) — reached through a dot import (import . %q: the bare identifier %s is that package's member; FR-36)",
		pkg.Name(), fn.Name(), pkg.Path(), pkg.Path(), fn.Name())
}

// refuseDotImportedValue: a dot-imported non-source stdlib function in VALUE
// position (`f := Intn`; `defer Intn(5)` / `go Intn(5)` evaluate the callee
// as a value) — the qualified spelling's FR-14 value-position refusal, import
// form named. The primitives lower at direct-call sites only (randintn.go
// `refuseRandIntnDeferGo` is the selector twin).
func (e *emitter) refuseDotImportedValue(fn *types.Func, pkg *types.Package) error {
	return unsup("dot-imported stdlib function %s.%s (import . %q) in value position: only DIRECT CALLS of modeled stdlib members lower (the primitives / the fmt desugar); the value shape is outside the modeled surface (package %q) — the qualified selector's refusal (FR-14), reached through a dot import (FR-36)",
		pkg.Name(), fn.Name(), pkg.Path(), pkg.Path())
}

// FR-37 (2026-10-07, lane `lane/fr37-dot-var-1007`; [USER] Mike 2026-10-07
// «We can run the FR-37 fix in a subagent right? Worth getting it done»,
// relayed by the [AGENT] coordinator — cite as relayed): a dot import also
// puts the package's VARIABLES in the file block (`import . "os"`;
// `len(Args)`). Such a `*types.Var` is no source package's global
// (`isPackageVar` keys on source scopes), so every identifier site fell
// through to `localIdent` and exported a bare
// `{"expr":"ident","local":0,"name":"Args"}` that the DECODER refused
// unnamed (the B6 c3 local-scope check) — fail closed, but the cause was
// not named, and the whole-wire decode failure masked every sibling
// refusal. The qualified spelling `os.Args` refuses by name in value
// position (FR-14). THE FIX: every identifier site that resolves a
// variable (`emitIdent`, the assignment-target arms, `emitAddressOf`, the
// lvalue arm) consults `dotImportedStdlibVar` BEFORE the local fallback and
// refuses by name — the variable has no driver-seeded cell (only source
// packages' globals are seeded; init design note §2). Go forbids a file
// block name to collide with the package block and the loader refuses dot
// imports of SOURCE packages (load.go), so a non-source package's
// package-scope variable reached as an identifier is exactly a dot-imported
// stdlib variable. Rows: stdlib-source/dot-import/{var-args,var-masking}.

// dotImportedStdlibVar reports whether obj — reached as a bare IDENTIFIER —
// is a package-level variable of a package other than the current one that
// is NOT a source package: exactly a dot-imported stdlib variable (above).
func (e *emitter) dotImportedStdlibVar(obj types.Object) (*types.Var, *types.Package, bool) {
	v, isVar := obj.(*types.Var)
	if !isVar || v == nil || v.IsField() {
		return nil, nil, false
	}
	pkg := v.Pkg()
	if pkg == nil || pkg == e.pkg || e.isSourcePackage(pkg) || v.Parent() != pkg.Scope() {
		return nil, nil, false
	}
	return v, pkg, true
}

// refuseDotImportedVar: the by-name refusal for a dot-imported stdlib
// variable in any shape (read, assignment target, address-of; index,
// range and selector uses reach it through their operand).
func (e *emitter) refuseDotImportedVar(v *types.Var, pkg *types.Package) error {
	return unsup("imported package-level variable %s.%s has no seeded cell — reached through a dot import (import . %q: the bare identifier %s is that package's variable; only source packages' globals are driver-seeded, and package %q is not source-through; FR-37)",
		pkg.Path(), v.Name(), pkg.Path(), v.Name(), pkg.Path())
}
