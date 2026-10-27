package main

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"sort"
)

// THE ENTRY RULE (BUG-125; [AGENT] lane frontend/main-undeclared-refuse-1013,
// 2026-10-13, under the [USER]'s ruling, Mike 2026-10-13, relayed: refuse
// the case rather than open the door to special-casing; support may come
// later; release-readiness row 41).
//
// By default the frontend exports a PROGRAM, and gc refuses to build a
// `package main` that declares no `func main` («function main is
// undeclared in the main package» — reported by gc's linker as
// `runtime.main_main·f: …`, with no source position; measured at the
// go1.26.5 pin on a one-file and a two-file package, 2026-10-13). So
// does this frontend: a `type-check:`-class refusal, gc's text, no wire.
//
// --subject (subjectMode) is the differential corpus's mode: the oracle
// harness supplies `main` around the subject function, and the machine's
// entry is the CLI's --function, so a main-less `package main` is the
// ordinary shape (494 of the 1457 directories under Corpus/coverage/exec
// that hold a .go file, 41 of them local sub-packages — counted
// 2026-10-13 at the train-9 stage by `find … -name '*.go' -printf '%h\n'
// | sort -u` and a grep for `^func main(`; BUG-125). Only this one rule
// is skipped; nothing else about the export changes, and on a package
// that declares `func main` the flag is a no-op.
//
// Reach (review LOW-1, 2026-10-13): a `func main` that lives only in a
// file gc's build constraints exclude (`//go:build ignore`, `!linux`) is
// gc's «undeclared» too, but file selection refuses the excluded file
// FIRST (fileselect.go, BUG-108's posture: an `unsupported` refusal
// naming the file, which the negative leg classes as frontend-reason,
// not as a rejection), so this rule never sees it; no negative row of
// that shape exists. Filename-convention exclusions (`main_windows.go`,
// `_entry.go`, `main_test.go`) are dropped silently and DO reach this
// rule (measured: refused, as gc does).
//
// This is the ONLY gc compilation-unit rule mirrored here — no
// whole-program mode (supporting such packages as gc would build them) is
// owed; the ruling left later support open.
//
// Not applied to a non-main (library) package: gc requires no main there.
// A `main` declared as something other than a function (`var main int`)
// or with a signature gc rejects is go/types' own error, reported before
// this check runs.
var subjectMode bool

func checkEntryDeclared(dir string, unit *sourcePkg) error {
	if subjectMode || unit.pkg == nil || unit.pkg.Name() != "main" {
		return nil
	}
	if _, ok := unit.pkg.Scope().Lookup("main").(*types.Func); ok {
		return nil
	}
	return fmt.Errorf("type-check: function main is undeclared in the main package (%s; gc reports this at link time, with no source position — the differential corpus's subject export passes --subject)", dir)
}

// THE REFERENCE RULE (BUG-220; [AGENT] lane frontend/fix-admission-1027,
// 2026-10-27, under the ruling of release-readiness row 41, [USER] Mike
// 2026-10-13, relayed: `main` stays UNEXPORTED in every mode — option 1;
// exporting it in default mode with its own `go run` oracle leg is a later
// maybe; exporting it in both modes was rejected).
//
// The emitter skips `func main` of the main unit (emit.go, the harness's
// contract), so a reference to it from ANY OTHER function — a call
// `main()`, a func value `f := main`, `defer main()`, `go main()`, from a
// function, a closure, a method or an init — was lowered as a reference to
// a function the wire does not carry, and the machine stopped `stuck`
// («GoCore function not found: main») on a legal program gc runs (the S20
// sweep's probes d7-live, d7c, d7d, d7e; measured 2026-10-27: gc prints 1
// on each). Under row 41's ruling the fix is the REFUSAL, by name, at
// export: a `package main` whose checked package references its own
// `main` from outside main's own body refuses as `unsupported` — an honest
// coverage gap, not a rejection class (gc accepts the program). A
// reference INSIDE main's body (a recursive main) is dropped with the body
// and is not a reference the wire can dangle. Both modes: in --subject
// mode the oracle harness drops `func main` too (tools/coverageharness),
// so such a subject does not compile on the oracle side either. Not a
// method named main, not a local named main, not an imported package's
// `main` function: those are other objects.
func checkEntryReferenced(fset *token.FileSet, unit *sourcePkg) error {
	if unit.pkg == nil || unit.pkg.Name() != "main" || unit.info == nil {
		return nil
	}
	mainFn, ok := unit.pkg.Scope().Lookup("main").(*types.Func)
	if !ok {
		return nil
	}
	var bodyStart, bodyEnd token.Pos
	for _, f := range unit.files {
		for _, d := range f.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok && fd.Recv == nil && fd.Name.Name == "main" {
				bodyStart, bodyEnd = fd.Pos(), fd.End()
			}
		}
	}
	var refs []*ast.Ident
	for id, obj := range unit.info.Uses {
		if obj != mainFn {
			continue
		}
		if bodyStart.IsValid() && id.Pos() >= bodyStart && id.Pos() < bodyEnd {
			continue // inside main's own body: dropped with it
		}
		refs = append(refs, id)
	}
	if len(refs) == 0 {
		return nil
	}
	// Deterministic refusal text (BUG-091): the first reference in file order.
	sort.Slice(refs, func(i, j int) bool { return refs[i].Pos() < refs[j].Pos() })
	return unsup("function main is referenced at %s outside its own body — the frontend never exports main (the wire holds the package's other functions; the differential corpus's --subject export drops main on the oracle side as well), so a call, a func value, a deferred call or a go statement naming it has no callee on the wire; refused by name at export rather than lowered to a reference the machine would report as function not found (BUG-220)", fset.Position(refs[0].Pos()))
}
