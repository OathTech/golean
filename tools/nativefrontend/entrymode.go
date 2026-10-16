package main

import (
	"fmt"
	"go/types"
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
