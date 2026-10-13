package main

// modfile.go — the module's `go` directive (BUG-109; whole-project review
// 2026-09-11 F2; RULED [USER] Mike 2026-09-11, verbatim, relayed by the
// [AGENT] coordinator: «Yes, refuse non-1.26»; lane fix/review-boundary-0911).
//
// The `go` command sets a package's LANGUAGE version from the `go`
// directive of the module that contains it (go.mod, found by walking up
// from the package directory), and the compiler changes meaning with it:
// under `go 1.21` a `for i := …` loop variable is shared across
// iterations (the review's probe prints 9), under `go 1.22`+ it is
// per-iteration (3). Before this file the frontend type-checked every
// directory at the PINNED language version (langversion.go, go1.26.5 →
// go1.26) and never read go.mod, so a `go 1.21` module was accepted and
// its meaning changed: 9 in gc, 3 here, a wrong answer with a clean
// export. This semantics implements the Go 1.26 language ONLY (the
// pin's third leg, docs/spec-sources.md); a module declaring another
// language version is REFUSED at export, by name.
//
// Scope: the lowered directory and every case-local imported package
// (load.go parseLocal) — each resolved to its NEAREST go.mod walking up
// to the filesystem root, exactly as the go command locates a module
// root (a nested go.mod is a different module and is judged on its
// own). No go.mod → the pinned 1.26, unchanged ([AGENT] detail recorded
// in BUG-109; the corpus's mode — Corpus/ carries no go.mod, and the
// oracle runs it under GO111MODULE=off). Stdlib source-through units
// come from the pinned GOROOT (stdlibsource.go, rev-checked), whose
// src/go.mod IS the pinned toolchain's; they are not re-judged here.
// OUT OF SCOPE, recorded: per-file `//go:build go1.N` constraints
// (already refused as reserved tags by langversion.go) and the
// `toolchain` directive (with GOTOOLCHAIN=local, the oracle pin guard's
// mode, it cannot switch toolchains). The directive is parsed by a small
// strict scanner — stdlib only, no x/mod — that refuses anything it does
// not understand rather than guess. Since 2026-10-13 (BUG-128, release-
// readiness row 39; RULED [USER] Mike 2026-10-13 «3, agree», relayed)
// the same scanner REFUSES a `godebug` line or block BY NAME: the go
// command folds the main module's godebug settings into the binary's
// defaults (cmd/go/internal/load/godebug.go defaultGODEBUG) and the
// model implements the Go 1.26 module defaults only — `panic(nil)`
// raises *runtime.PanicNilError, the differential oracle is pinned with
// GODEBUG=panicnil=0 (scripts/diff-coverage). gc reads only the MAIN
// module's godebug lines; the refusal fires in every go.mod this scanner
// reads (a nested module's too), by name, rather than re-deriving which
// module is main. The source twin `//go:debug` is directives.go.

import (
	"bufio"
	"go/version"
	"os"
	"path/filepath"
	"strings"
)

// findGoMod returns the nearest go.mod at or above dir ("" if none),
// following the go command's module-root search. dir is made absolute
// first so the walk terminates at the filesystem root.
func findGoMod(dir string) (string, error) {
	abs, err := filepath.Abs(dir)
	if err != nil {
		return "", unsup("module directive: cannot resolve %s (%v) — fail closed", dir, err)
	}
	for d := abs; ; d = filepath.Dir(d) {
		candidate := filepath.Join(d, "go.mod")
		if fi, err := os.Stat(candidate); err == nil && !fi.IsDir() {
			return candidate, nil
		}
		if filepath.Dir(d) == d {
			return "", nil
		}
	}
}

// goModVerbs: what this scanner does with each directive of gc's go.mod
// grammar at the pin (cmd/vendor/golang.org/x/mod/modfile/rule.go, the
// strict parser's verb switch — the go command refuses any other first
// token: «unknown directive: <verb>», measured). x/mod's lexer makes `(`
// and `)` tokens of their own, so `godebug(` is `godebug` `(` (measured:
// gc honours it); the scanner splits them off before reading the verb.
//
//	module                 ACCEPTED: the module path names nothing the
//	                       lowering reads (imports are stdlib or case-local).
//	go                     JUDGED: must be the pinned language version
//	                       (BUG-109).
//	toolchain              ACCEPTED only when it names the pinned toolchain
//	                       (go1.26.5); any other name REFUSED — under
//	                       GOTOOLCHAIN=auto a consumer would be switched to
//	                       a toolchain the semantics is not measured against
//	                       (the apparatus runs GOTOOLCHAIN=local, where the
//	                       line is inert, measured).
//	godebug                REFUSED by name, line or block, with or without
//	                       the blank before `(` (BUG-128).
//	require, exclude,      ACCEPTED, line or block: the module graph cannot
//	replace, retract       reach the lowered program — its imports are the
//	                       standard library (from the pinned GOROOT) and
//	                       case-local packages (relative paths), neither
//	                       resolved through requires or replaces.
//	tool, ignore           ACCEPTED: build-time directives of the go command
//	                       (`go tool` dependencies; directories `./...`
//	                       skips), never the compiled program.
//	anything else          REFUSED by name: gc refuses the go.mod, and
//	                       nothing unknown is guessed here.
var goModAccepted = map[string]bool{"module": true, "require": true, "exclude": true, "replace": true, "retract": true, "tool": true, "ignore": true}

// goDirective returns the language version named by the go.mod's `go`
// directive as go/version's Lang form ("go1.21"), after judging every
// other directive by goModVerbs. Fail closed: no `go` directive (the go
// command then assumes go 1.16 — another language version), a repeated
// directive, a version go/version cannot parse, a godebug directive, a
// toolchain other than the pin, or a verb the grammar does not know are
// refusals naming the file.
func goDirective(path string) (string, error) {
	f, err := os.Open(path)
	if err != nil {
		return "", unsup("module directive: cannot read %s (%v) — fail closed", path, err)
	}
	defer f.Close()
	pinnedTC, err := pinnedToolchainName()
	if err != nil {
		return "", err
	}
	found := ""
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 0, 64*1024), 1<<20)
	inBlock := false
	parens := strings.NewReplacer("(", " ( ", ")", " ) ")
	for sc.Scan() {
		raw := sc.Text()
		line := raw
		if i := strings.Index(line, "//"); i >= 0 {
			line = line[:i]
		}
		fields := strings.Fields(parens.Replace(line))
		if len(fields) == 0 {
			continue
		}
		// Block bodies (`require (` … `)`) carry no directive verb; skipped
		// so a module path or version token spelled like a verb inside one
		// cannot be mistaken for it. Only ACCEPTED verbs open a block —
		// `godebug (` is refused before this point.
		if inBlock {
			if fields[0] == ")" {
				inBlock = false
			}
			continue
		}
		verb := fields[0]
		switch {
		case verb == "godebug":
			return "", unsup("module directive: %s sets godebug (%s) — GODEBUG settings are not modeled: the semantics is the Go 1.26 module defaults (panic(nil) raises *runtime.PanicNilError; the differential oracle is pinned with GODEBUG=panicnil=0); RULED [USER] 2026-10-13: refuse by name (fail closed)", path, strings.TrimSpace(raw))
		case verb == "go":
			if len(fields) != 2 {
				return "", unsup("module directive: %s has a malformed go directive %q — fail closed", path, strings.TrimSpace(line))
			}
			if found != "" {
				return "", unsup("module directive: %s repeats the go directive (%s and %s) — the go command refuses this too; fail closed", path, found, fields[1])
			}
			found = fields[1]
		case verb == "toolchain":
			if len(fields) != 2 {
				return "", unsup("module directive: %s has a malformed toolchain directive %q — fail closed", path, strings.TrimSpace(line))
			}
			if fields[1] != pinnedTC {
				return "", unsup("module directive: %s names toolchain %s; the oracle is pinned to %s — under GOTOOLCHAIN=auto a consumer would build with a toolchain the semantics is not measured against (the apparatus runs GOTOOLCHAIN=local, where the line is inert); refuse by name (fail closed)", path, fields[1], pinnedTC)
			}
		case goModAccepted[verb]:
			if fields[len(fields)-1] == "(" {
				inBlock = true
			}
		default:
			return "", unsup("module directive: %s has a directive this scanner does not know (%q) — the go command refuses the go.mod («unknown directive: %s»), and nothing unknown is guessed here; fail closed", path, strings.TrimSpace(line), verb)
		}
	}
	if err := sc.Err(); err != nil {
		return "", unsup("module directive: cannot scan %s (%v) — fail closed", path, err)
	}
	if found == "" {
		return "", unsup("module directive: %s has no go directive; the go command assumes go 1.16 for such a module — GoLean implements the Go 1.26 language only", path)
	}
	lang := version.Lang("go" + found)
	if lang == "" {
		return "", unsup("module directive: %s declares go %s, which go/version cannot parse — fail closed", path, found)
	}
	return lang, nil
}

// refuseForeignModuleVersion refuses the export when the module
// containing dir declares a language version other than the pinned one.
// The refusal text is the BUG-109 form: `go.mod declares go 1.21; GoLean
// implements the Go 1.26 language only`.
func refuseForeignModuleVersion(dir string) error {
	modPath, err := findGoMod(dir)
	if err != nil {
		return err
	}
	if modPath == "" {
		return nil // no module: the pinned language version, unchanged
	}
	lang, err := goDirective(modPath)
	if err != nil {
		return err
	}
	pinned, err := pinnedLangVersion()
	if err != nil {
		return err
	}
	if lang != pinned {
		return unsup("%s declares go %s; GoLean implements the Go %s language only (the module's language version changes the program's meaning — e.g. the go1.22 per-iteration loop variable; RULED [USER] 2026-09-11: refuse non-1.26)", modPath, strings.TrimPrefix(lang, "go"), strings.TrimPrefix(pinned, "go"))
	}
	return nil
}
