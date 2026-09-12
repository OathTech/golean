package main

// fileselect.go — the package FILE SET, taken from go/build under the
// PINNED target (BUG-108; whole-project review 2026-09-11 F1; lane
// fix/review-boundary-0911, [AGENT]).
//
// Before this file the frontend parsed EVERY non-test `*.go` file of a
// directory (`parser.ParseDir` + `nonTestGoFile`, in main.go and
// load.go), so files gc never compiles — a leading `_` or `.`, or a
// `_GOOS`/`_GOARCH`/`_GOOS_GOARCH` suffix naming another target — were
// lowered and their `init` effects ran: `main.go` + `extra_windows.go
// { func init() { x = 2 } }` answered 2 where `go run .` prints 1, with a
// clean export and no refusal (the review's F1; corpus rows
// source-selection/excluded-init/*). The selection rules are gc's
// (go/build `matchFile` + `goodOSArchFile`), so the file set is taken
// from go/build itself — `build.Context.ImportDir` under a Context
// pinned to the platform's target — never re-implemented here.
//
// THE PINNED TARGET is gc on linux/amd64, the oracle host's realization
// and the machine's `Platform` (GoLean/GoCore/Platform.lean `gcAmd64`:
// the layout half of the same pin); cgo ENABLED, as the oracle's
// `CGO_ENABLED=1` default (the runner's `-race` draws require it) —
// with cgo enabled go/build lists `import "C"` files as CgoFiles, which
// is what lets them be REFUSED by name below (with cgo disabled they
// would fall into IgnoredGoFiles and vanish); no `-tags` (the runner
// passes none). The target is recorded on the wire (`buildContext`,
// emit.go) and the decoder refuses a wire lowered for any other target
// (NativeToIR.lean decodeProgram): the selection is part of what the
// wire means.
//
// Fail closed, by name, on everything gc would treat differently from
// "these Go files and nothing else": InvalidGoFiles (a selected file
// whose header gc cannot read — gc's error, not ours to skip),
// CgoFiles (cgo is out of scope), assembly/.syso/C-family sources (gc
// would assemble or link them), a MultiplePackageError or NoGoError
// from go/build (gc's own refusals), and — the pre-existing
// build-constraint policy of langversion.go, UNCHANGED — any selected
// file carrying a reserved-tag or excluding constraint. An EXCLUDED
// file is dropped silently only when its exclusion is determinate on
// every host: a `_`/`.` prefix, or a GOOS/GOARCH suffix with no build
// constraint in its header. An excluded file that DOES carry a
// constraint is judged by the same policy as an included one (reserved
// tag or excluding expression → refuse): this over-refuses a
// `x_windows.go` that also says `//go:build cgo` (gc simply ignores
// it), which is the fail-closed direction and is recorded here rather
// than silently resolved by reimplementing go/build's suffix rule.

import (
	"bufio"
	"go/ast"
	"go/build"
	"go/build/constraint"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// The pinned selection target. Mirror of GoLean/GoCore/Platform.lean
// `gcAmd64` (layout) and of NativeToIR.lean `pinnedSelectionTarget`
// (the decoder's acceptance check) — three spellings of ONE pin; the
// decoder refuses a wire whose record disagrees with its own.
const (
	pinnedGOOS       = "linux"
	pinnedGOARCH     = "amd64"
	pinnedCompiler   = "gc"
	pinnedCgoEnabled = true
)

// pinnedBuildContext is go/build's Default with the target pinned:
// GOOS/GOARCH/Compiler/CgoEnabled set explicitly (never read from the
// host environment), no -tags, UseAllFiles off. ReleaseTags and
// ToolTags stay the running toolchain's (the pinned go1.26.5); they
// only matter to `//go:build` evaluation, and every constraint that
// mentions a reserved tag is refused before evaluation by the
// langversion.go policy, so no host-configuration bit reaches the
// selected set.
func pinnedBuildContext() build.Context {
	ctxt := build.Default
	ctxt.GOOS = pinnedGOOS
	ctxt.GOARCH = pinnedGOARCH
	ctxt.Compiler = pinnedCompiler
	ctxt.CgoEnabled = pinnedCgoEnabled
	ctxt.BuildTags = nil
	ctxt.UseAllFiles = false
	ctxt.GOPATH = "" // ImportDir takes a directory; no path resolution
	return ctxt
}

// buildContextRecord is the wire's program-level `buildContext` field:
// the target the file set was selected for. The decoder requires it
// and refuses any value other than its own pin.
func buildContextRecord() map[string]any {
	return map[string]any{
		"goos":       pinnedGOOS,
		"goarch":     pinnedGOARCH,
		"compiler":   pinnedCompiler,
		"cgoEnabled": pinnedCgoEnabled,
		"buildTags":  []any{},
	}
}

// selectPackageFiles returns the parsed files gc would compile for the
// package in dir under the pinned target, in lexical filename order (the
// go command's directory-mode presentation — the E8 realization site
// main.go/load.go used to sort by hand; go/build's ReadDir order is the
// same sort, re-sorted here so the order is this function's contract,
// not a property of the reader).
func selectPackageFiles(fset *token.FileSet, dir string) ([]*ast.File, error) {
	ctxt := pinnedBuildContext()
	pkg, err := ctxt.ImportDir(dir, 0)
	if err != nil {
		// go/build's own refusals, verbatim behind our name: a
		// MultiplePackageError (two package clauses among the SELECTED
		// files — an excluded file's clause is never read), a
		// NoGoError (nothing selected), an unreadable directory, or
		// the first InvalidGoFiles error.
		return nil, unsup("file selection in %s under the pinned target %s/%s (%s, cgo=%t): %v — gc would refuse this directory; fail closed", dir, pinnedGOOS, pinnedGOARCH, pinnedCompiler, pinnedCgoEnabled, err)
	}
	if len(pkg.InvalidGoFiles) > 0 {
		// Reached when go/build recorded a bad file but returned no
		// error (it returns the FIRST badGoError as err, so this is a
		// belt-and-braces arm: a selected file gc cannot read is never
		// skipped).
		return nil, unsup("file selection in %s: gc cannot read %s (InvalidGoFiles) — a selected file gc refuses is not ours to skip; fail closed", dir, strings.Join(pkg.InvalidGoFiles, ", "))
	}
	if len(pkg.CgoFiles) > 0 {
		return nil, unsup("file selection in %s: %s import \"C\" (CgoFiles) — cgo is outside the modeled fragment; fail closed", dir, strings.Join(pkg.CgoFiles, ", "))
	}
	if extra := nonGoSources(pkg); len(extra) > 0 {
		return nil, unsup("file selection in %s: gc would assemble/compile/link non-Go sources %s — outside the modeled fragment; fail closed", dir, strings.Join(extra, ", "))
	}
	// Excluded files (GOOS/GOARCH suffix or build constraint; the
	// `_`/`.`-prefixed ones go/build does not even list): a constraint in
	// the header is judged by the standing policy; a header without one
	// means the exclusion was the filename's, determinate on every host.
	for _, name := range pkg.IgnoredGoFiles {
		if strings.HasSuffix(name, "_test.go") {
			continue // test files are never part of the program (as before)
		}
		if err := refuseIgnoredFileConstraints(dir, name); err != nil {
			return nil, err
		}
	}
	names := append([]string(nil), pkg.GoFiles...)
	sort.Strings(names)
	files := make([]*ast.File, 0, len(names))
	for _, name := range names {
		f, err := parser.ParseFile(fset, filepath.Join(dir, name), nil, parser.ParseComments)
		if err != nil {
			return nil, err
		}
		files = append(files, f)
	}
	if len(files) == 0 {
		return nil, unsup("file selection in %s: no Go files selected under the pinned target (fail closed)", dir)
	}
	// The SELECTED files' build constraints: the standing langversion.go
	// policy (reserved tags refuse; a custom-tag constraint must be inert),
	// applied here so selection and policy are ONE site for both the main
	// package and every imported unit — previously each caller ran it.
	if err := refuseBuildConstrainedFiles(fset, files); err != nil {
		return nil, err
	}
	return files, nil
}

// nonGoSources lists the sources gc would hand to the assembler, the C
// toolchain or the linker. HFiles are omitted: gc reads headers only
// through cgo/assembly, both refused separately, so a stray .h is inert.
func nonGoSources(pkg *build.Package) []string {
	var out []string
	out = append(out, pkg.SFiles...)
	out = append(out, pkg.SysoFiles...)
	out = append(out, pkg.CFiles...)
	out = append(out, pkg.CXXFiles...)
	out = append(out, pkg.MFiles...)
	out = append(out, pkg.FFiles...)
	out = append(out, pkg.SwigFiles...)
	out = append(out, pkg.SwigCXXFiles...)
	sort.Strings(out)
	return out
}

// refuseIgnoredFileConstraints scans an EXCLUDED file's header — the
// leading `//` and `/* */` comment lines before the package clause, as
// go/build's own header reader does — for build-constraint lines and
// judges each by the langversion.go policy. A header with no constraint
// line means go/build excluded the file for its NAME, which gc decides
// identically on every host: nothing to refuse. A header that does not
// parse is a filename-excluded file gc never opens (a constraint-
// excluded file's header was read successfully by go/build, else it
// would be an InvalidGoFile); its lines are still scanned textually, so
// a constraint line in garbage is refused rather than skipped.
func refuseIgnoredFileConstraints(dir, name string) error {
	path := filepath.Join(dir, name)
	f, err := os.Open(path)
	if err != nil {
		return unsup("file selection in %s: cannot read excluded file %s (%v) — fail closed", dir, name, err)
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 0, 64*1024), 1<<20)
	inBlock := false
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		if inBlock {
			if i := strings.Index(line, "*/"); i >= 0 {
				inBlock = false
				line = strings.TrimSpace(line[i+2:])
			} else {
				continue
			}
		}
		if line == "" {
			continue
		}
		if strings.HasPrefix(line, "/*") {
			if !strings.Contains(line, "*/") {
				inBlock = true
			}
			continue
		}
		if !strings.HasPrefix(line, "//") {
			break // the package clause (or anything else): the header is over
		}
		if constraint.IsGoBuild(line) || constraint.IsPlusBuild(line) {
			if err := judgeBuildConstraintLine(path, line); err != nil {
				return err
			}
		}
	}
	if err := sc.Err(); err != nil {
		return unsup("file selection in %s: cannot scan excluded file %s (%v) — fail closed", dir, name, err)
	}
	return nil
}
