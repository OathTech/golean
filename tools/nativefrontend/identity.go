package main

// identity.go — the multi-package identity boundary (raft W1.1,
// docs/2026-08-18_multipackage-identity.md). Wire TypeId/FuncId/global
// qualifiers are minted HERE (and in qualifiedTypeName, which shares
// pkgQualifier): import-path-qualified, main-package names bare —
// grammar injectivity per the design note §1. GoCore sees only the
// resulting opaque strings.

import (
	"go/types"
	"sort"
	"strings"
)

// setUnits installs the loaded source units (program initialization
// order, main LAST) and derives the membership views.
func (e *emitter) setUnits(units []*sourcePkg) {
	e.units = units
	e.srcPkgSet = map[*types.Package]*sourcePkg{}
	for _, u := range units {
		e.srcPkgSet[u.pkg] = u
	}
	e.mainPkg = units[len(units)-1].pkg
}

// setUnit switches the emitter's per-package state to the unit whose
// declarations are being emitted. e.pkg feeds go/types visibility
// (LookupFieldOrMethod) and the scope checks; e.info is the unit's own
// type-checker record (Uses/Defs/Types/Selections/Instances/InitOrder
// are AST-node-keyed, and the nodes belong to exactly one unit).
func (e *emitter) setUnit(u *sourcePkg) {
	e.pkg = u.pkg
	e.info = u.info
	e.curUnit = u
}

// isLibraryPackage: the package is a stdlib source-through LIBRARY unit
// (stdlibsource.go) — a source package (isSourcePackage is true of it
// too) whose declarations are emitted reachability-pruned and whose
// calls never route through the user-package shims.
func (e *emitter) isLibraryPackage(pkg *types.Package) bool {
	if pkg == nil || e.units == nil {
		return false
	}
	u := e.srcPkgSet[pkg]
	return u != nil && u.library
}

// isSourcePackage: the package is part of the program under lowering
// (main or a case-local import) — as opposed to stdlib. Nil-units
// fallback: the single directly-constructed package.
func (e *emitter) isSourcePackage(pkg *types.Package) bool {
	if pkg == nil {
		return false
	}
	if e.units == nil {
		return pkg == e.pkg
	}
	return e.srcPkgSet[pkg] != nil
}

// isMainPackage: the subject namespace (bare FuncIds).
func (e *emitter) isMainPackage(pkg *types.Package) bool {
	if e.units == nil {
		return pkg == e.pkg
	}
	return pkg == e.mainPkg
}

// isSourceScope reports whether a variable's parent scope is some
// source package's scope — the package-level-variable classification
// (globals resolve to driver-seeded cells, never captures).
func (e *emitter) isSourceScope(parent *types.Scope) bool {
	if parent == nil {
		return false
	}
	if e.units == nil {
		return parent == e.pkg.Scope()
	}
	for _, u := range e.units {
		if parent == u.pkg.Scope() {
			return true
		}
	}
	return false
}

// pkgQualifier returns the wire qualifier for a declaring package: its
// IMPORT PATH (Go's identity — the BUG-010 fix). Dotted paths break
// the key grammar (the '.' separator; identity note §3.2) and are
// RECORDED here for checkKeyPathGrammar's fail-closed refusal.
func (e *emitter) pkgQualifier(pkg *types.Package) string {
	p := pkg.Path()
	if strings.Contains(p, ".") {
		if e.badKeyPaths == nil {
			e.badKeyPaths = map[string]bool{}
		}
		e.badKeyPaths[p] = true
	}
	return p
}

// funcWireName mints the wire FuncId of a PACKAGE-LEVEL function
// (methods key by receiver TypeId instead — never routed here):
// main-package and universe names stay BARE (the subject namespace;
// dot-free, so they cannot collide with qualified keys), source
// packages qualify by import path. NON-source (stdlib) functions stay
// bare too: no static-call path exists for them except shims/externs,
// and the recorded stdlib dot-import defect (stdlibshim.go FAIL-CLOSED
// RULES) keeps its exact shape — neither fixed nor widened here.
func (e *emitter) funcWireName(fn *types.Func) string {
	pkg := fn.Pkg()
	if pkg == nil || e.isMainPackage(pkg) || !e.isSourcePackage(pkg) {
		return fn.Name()
	}
	return e.pkgQualifier(pkg) + "." + fn.Name()
}

// globalWireName mints the wire NAME of a package-level variable (the
// gid stays the identity; the name feeds the decoder's duplicate
// refusal and human-readable wires).
func (e *emitter) globalWireName(v *types.Var) string {
	pkg := v.Pkg()
	if pkg == nil || e.isMainPackage(pkg) || !e.isSourcePackage(pkg) {
		return v.Name()
	}
	return e.pkgQualifier(pkg) + "." + v.Name()
}

// initFuncWireName mints the reserved id of the unit's n-th init()
// function: `$initN` for main (unchanged), `<path>.$initN` otherwise.
func (e *emitter) initFuncWireName(u *sourcePkg, n int) string {
	name := "$init" + itoa(n)
	if u.pkg == e.mainPkg {
		return name
	}
	return e.pkgQualifier(u.pkg) + "." + name
}

// checkKeyPathGrammar fails the export when a dotted import path
// reached a wire qualifier: `TypeId.unqualified` (the reflect-Name
// observation contract) strips at the FIRST '.', and the key
// injectivity argument (identity note §1) needs dot-free qualifiers.
// Fail closed at the boundary that minted the key, like the
// package-name collision check this replaces.
func (e *emitter) checkKeyPathGrammar() error {
	if len(e.badKeyPaths) == 0 {
		return nil
	}
	paths := make([]string, 0, len(e.badKeyPaths))
	for p := range e.badKeyPaths {
		paths = append(paths, p)
	}
	sort.Strings(paths)
	return unsup("dotted import path(s) in wire identity keys: %v — the key grammar reserves '.' for the qualifier/name separator (docs/2026-08-18_multipackage-identity.md §3); vendor at dot-free paths", paths)
}
