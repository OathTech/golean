package main

// stdlibsource.go — the LIBRARY SOURCE ROOT (stdlib source-through,
// slice 1 `stdlib-source-1`, 2026-09-03; design memo
// docs/2026-09-03_stdlib-boundary-design.md §2.1/§2.3/§6, gates G1/G3/
// G4/G8/G9 ruled AS RECOMMENDED by the [USER] (Mike, 2026-09-03,
// relayed by the [AGENT] coordinator — cited as relayed, not firsthand).
//
// THE SHAPE. An import path on the ALLOWED-LIBRARY list below resolves to
// the real GOROOT source at the oracle pin (`deps/go/src/<path>`, rev
// go1.26.5 = scripts/setup-deps' `go` row), loaded as an ordinary SOURCE
// UNIT by the multi-package loader (load.go) — parsed, type-checked whole
// with go/types, and EMITTED REACHABILITY-PRUNED (stdlibreach.go): only
// the declarations the program reaches lower; every reached declaration
// the pipeline cannot lower becomes the existing per-declaration
// quarantine stub (emit.go H-3), so a call to it refuses BY NAME at run
// time. Nothing is pasted into the user's package; FuncIds are the
// path-qualified ones the identity design mints (`strings.Fields`,
// `internal/strconv.FormatUint`). No text here is ours — the whole point
// of the slice is ZERO hand-written library text.
//
// FILE SELECTION (the modeled member). go/build's selection under the
// ORACLE'S build context — GOOS=linux GOARCH=amd64 CgoEnabled=false,
// release tags of the pinned toolchain — is the file set gc compiled for
// the oracle binary; build-constrained library files are therefore
// RESOLVED here, not refused (langversion.go's refusal is for USER files,
// where a constraint means file-set selection outside the modeled
// fragment). The assembly-backed leaves are then swapped for their
// portable upstream twins by the tracked SUBSTITUTION TABLE
// (stdlib-substitutions.tsv, go:embed): drop `*_native.go`/`*_amd64.go`,
// add `*_generic.go`. Both directions fail closed (a drop that was not
// selected, an add that does not exist).
//
// FAIL-CLOSED RULES:
//   - The source root must be at the pin: `<root>/../VERSION` must name
//     exactly the pinned toolchain (the inittask table's header, = the
//     oracle). Absent or different → refuse, naming both.
//   - Every selected file's sha256 must equal its row in the tracked
//     LIBRARY PIN (baselines/stdlib-pin.tsv); a file with no row, or a
//     differing hash → refuse by path. The pin is re-derived by
//     `nativefrontend --stdlib-pin-manifest` and compared by
//     scripts/check-frontend-pins (staleness in either direction).
//   - `//go:linkname` PULL directives (a local var/func whose body lives
//     in the runtime) are recorded per unit: a body-less function
//     quarantines (emitFuncDecl's standing refusal, cause-named), a
//     linknamed VARIABLE is poisoned like an H-11 quarantined global —
//     reading it refuses instead of yielding a zero-seeded cell (the
//     silent-wrong-answer shape: math/bits' `overflowError`).
//   - Anything outside the allowed list keeps today's refusals verbatim.

import (
	"crypto/sha256"
	_ "embed"
	"encoding/hex"
	"fmt"
	"go/ast"
	"go/build"
	"go/parser"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
)

// stdlibSourceAllowed is the ALLOWED-LIBRARY list of slice 1: import
// path -> the reason it is on the list. Everything reachable from the
// six retired shims' bodies plus the packages' own transitive PURE
// dependencies (memo §6 mechanism 1). Widening is a register change
// (docs/stdlib-admission-register.md; scripts/check-stdlib-register
// compares this table to the register).
var stdlibSourceAllowed = map[string]string{
	"strings":              "slice-1 target (Fields, TrimSpace, Split retired from shims); pure Go at function granularity given the bytealg substitution — Builder stays the E5-T shadow model until slice 2's overlay",
	"strconv":              "slice-1 target (FormatUint, FormatInt retired from shims); thin wrappers over internal/strconv; ParseUint's shim is RETAINED (its error path reaches internal/stringslite.Clone's unsafe.String — overlay pending, slice 2)",
	"internal/strconv":     "strconv's implementation package; pure Go except deps.go's four float-bits casts (unreached by the integer paths; quarantine by name if reached)",
	"internal/stringslite": "strings/strconv's shared Index/Cut/Clone helpers; Clone uses unsafe.String (quarantines by name when reached)",
	"internal/bytealg":     "the byte-search leaves strings.Index/Count/Split reach; assembly on amd64, swapped for the package's own *_generic.go twins by stdlib-substitutions.tsv",
	"unicode":              "unicode.IsSpace and its White_Space RangeTable (strings.Fields/TrimSpace's non-ASCII path); pure tables, reached ones only",
	"unicode/utf8":         "rune decoding used by strings' non-ASCII paths and explode; pure",
	"math/bits":            "internal/strconv's formatBits uses bits.TrailingZeros; pure except the two runtime-linknamed error VALUES (poisoned by the linkname rule)",
	"errors":               "errors.New for strconv's ErrRange/ErrSyntax package variables (pure); the user-facing errors.New SHIM is not retired this slice",
}

//go:embed stdlib-substitutions.tsv
var stdlibSubstitutionsTSV string

// stdlibSubstitution is one row of the substitution table.
type stdlibSubstitution struct {
	pkg, drop, add, reason string
}

// parseStdlibSubstitutions parses the embedded table. A malformed row
// is a refusal at first use, never a silently skipped line.
func parseStdlibSubstitutions(tsv string) ([]stdlibSubstitution, error) {
	var rows []stdlibSubstitution
	for n, line := range strings.Split(tsv, "\n") {
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		cols := strings.Split(line, "\t")
		if len(cols) != 4 || cols[0] == "" || cols[1] == "" || cols[2] == "" || cols[3] == "" {
			return nil, unsup("stdlib-substitutions.tsv line %d is malformed (want package<TAB>drop<TAB>add<TAB>reason, all non-empty): %q", n+1, line)
		}
		rows = append(rows, stdlibSubstitution{pkg: cols[0], drop: cols[1], add: cols[2], reason: cols[3]})
	}
	return rows, nil
}

// The two library-root knobs (main.go flags). Defaults are REPO-RELATIVE:
// every script that drives the frontend runs it from the repo root
// (scripts/diff-coverage, check-frontend-pins, gotest-triage).
var stdlibSrcRoot = "deps/go/src"
var stdlibPinPath = "baselines/stdlib-pin.tsv"

// pinnedToolchainName is the oracle toolchain the embedded inittask
// table was generated for ("go1.26.5") — the single in-binary statement
// of the pin (langversion.go derives the language version from the same
// header line).
func pinnedToolchainName() (string, error) {
	for _, line := range strings.Split(stdInitTableTSV, "\n") {
		if !strings.HasPrefix(line, "# toolchain:") {
			continue
		}
		fields := strings.Fields(strings.TrimPrefix(line, "# toolchain:"))
		if len(fields) == 0 {
			break
		}
		return fields[0], nil
	}
	return "", unsup("embedded inittask-std.tsv has no '# toolchain:' header line — cannot derive the pinned toolchain (fail closed)")
}

// checkStdlibSrcRev refuses unless <root>/../VERSION names the pinned
// toolchain exactly. Called once per program that loads a library unit.
func checkStdlibSrcRev() error {
	want, err := pinnedToolchainName()
	if err != nil {
		return err
	}
	versionFile := filepath.Join(stdlibSrcRoot, "..", "VERSION")
	data, err := os.ReadFile(versionFile)
	if err != nil {
		return unsup("stdlib source root %q is not a Go checkout at the pin: cannot read %s (%v) — run scripts/setup-deps --only go (fail closed)", stdlibSrcRoot, versionFile, err)
	}
	first := strings.TrimSpace(strings.SplitN(string(data), "\n", 2)[0])
	if first != want {
		return unsup("stdlib source root %q is at %q, the oracle pin is %q (%s vs inittask-std.tsv header) — rev drift is resolved by hand, never floated (fail closed)", stdlibSrcRoot, first, want, versionFile)
	}
	return checkHostToolchainPinned(runtime.Version(), want)
}

// checkHostToolchainPinned refuses unless the frontend's OWN toolchain is
// the pinned one (audit fix round F4). The library units are type-checked
// against the HOST's export data for the packages outside the allowed
// list (`importer.Default()` in load.go: internal/cpu, internal/abi,
// internal/reflectlite, io, sync, iter) — a content channel the source
// pin does not cover. Pinning the host toolchain closes the rev half of
// it; the residual — that export data is the host's compiled view, not
// the checkout's text — is recorded in the admission register
// (internal/bytealg.go's `unsafe.Offsetof(cpu.X86…)` constants are the
// one place a host-layout fact could enter, and they are unreached).
func checkHostToolchainPinned(host, want string) error {
	if host != want {
		return unsup("the frontend runs on toolchain %q but the oracle pin is %q: the library units would be type-checked against the HOST's export data for their unmodeled imports (internal/cpu, internal/abi, internal/reflectlite, io, sync, iter) — a different toolchain is a different library; fail closed (run the frontend with the pinned go)", host, want)
	}
	return nil
}

// libraryBuildContext is the ORACLE's build context: what gc selected
// when it compiled the standard library the differential runs against.
func libraryBuildContext() build.Context {
	ctx := build.Default
	ctx.GOOS = "linux"
	ctx.GOARCH = "amd64"
	ctx.CgoEnabled = false
	ctx.Compiler = "gc"
	ctx.GOROOT = filepath.Clean(filepath.Join(stdlibSrcRoot, ".."))
	ctx.GOPATH = ""
	return ctx
}

// selectLibraryFiles returns the ABSOLUTE-or-root-relative paths (sorted,
// lexical file-name order — the E8 directory-mode member, same as
// main.go/parseLocal) of the files the frontend lowers for one allowed
// library package: go/build's selection under the oracle context, minus
// the substitution table's drops, plus its adds. Fail closed on every
// table mismatch.
func selectLibraryFiles(path string) ([]string, error) {
	if _, allowed := stdlibSourceAllowed[path]; !allowed {
		return nil, unsup("internal: selectLibraryFiles(%q) for a package outside the allowed-library list", path)
	}
	dir := filepath.Join(stdlibSrcRoot, filepath.FromSlash(path))
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil, unsup("stdlib source package %q: cannot read %s (%v) — fail closed", path, dir, err)
	}
	ctx := libraryBuildContext()
	selected := map[string]bool{}
	for _, ent := range entries {
		name := ent.Name()
		if ent.IsDir() || filepath.Ext(name) != ".go" || strings.HasSuffix(name, "_test.go") {
			continue
		}
		ok, err := ctx.MatchFile(dir, name)
		if err != nil {
			return nil, unsup("stdlib source package %q: go/build could not evaluate %s (%v) — fail closed", path, name, err)
		}
		if ok {
			selected[name] = true
		}
	}
	subs, err := parseStdlibSubstitutions(stdlibSubstitutionsTSV)
	if err != nil {
		return nil, err
	}
	adds := map[string]bool{}
	for _, s := range subs {
		if s.pkg != path {
			continue
		}
		if !selected[s.drop] {
			return nil, unsup("stdlib-substitutions.tsv: %s/%s is listed as a DROP but go/build did not select it under the oracle context (linux/amd64) — the table is stale for this pin (fail closed)", path, s.drop)
		}
		delete(selected, s.drop)
		if _, err := os.Stat(filepath.Join(dir, s.add)); err != nil {
			return nil, unsup("stdlib-substitutions.tsv: %s/%s is listed as an ADD but does not exist at the pin (%v) — fail closed", path, s.add, err)
		}
		adds[s.add] = true
	}
	for a := range adds {
		selected[a] = true
	}
	out := make([]string, 0, len(selected))
	for name := range selected {
		out = append(out, filepath.Join(dir, name))
	}
	sort.Strings(out)
	if len(out) == 0 {
		return nil, unsup("stdlib source package %q: no files selected under the oracle context — fail closed", path)
	}
	return out, nil
}

// libraryPinKey is the pin's path column for a selected file: slash-
// separated, relative to the source root ("strings/strings.go").
func libraryPinKey(file string) (string, error) {
	rel, err := filepath.Rel(stdlibSrcRoot, file)
	if err != nil {
		return "", unsup("stdlib pin: cannot relativize %s to %s (%v)", file, stdlibSrcRoot, err)
	}
	return filepath.ToSlash(rel), nil
}

func sha256File(path string) (string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:]), nil
}

// loadStdlibPin reads baselines/stdlib-pin.tsv: path<TAB>sha256 rows,
// '#' comments. Missing or malformed → refuse.
func loadStdlibPin() (map[string]string, error) {
	data, err := os.ReadFile(stdlibPinPath)
	if err != nil {
		return nil, unsup("stdlib library pin %s unreadable (%v): library source-through cannot be certified against the pin — fail closed (regenerate with `nativefrontend --stdlib-pin-manifest` and commit deliberately with the reason)", stdlibPinPath, err)
	}
	pin := map[string]string{}
	for n, line := range strings.Split(string(data), "\n") {
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		cols := strings.Split(line, "\t")
		if len(cols) != 2 || cols[0] == "" || len(cols[1]) != 64 {
			return nil, unsup("stdlib library pin %s line %d is malformed (want path<TAB>sha256): %q", stdlibPinPath, n+1, line)
		}
		if _, dup := pin[cols[0]]; dup {
			return nil, unsup("stdlib library pin %s line %d: duplicate row for %s", stdlibPinPath, n+1, cols[0])
		}
		pin[cols[0]] = cols[1]
	}
	return pin, nil
}

// checkLibraryFilesPinned verifies every selected file against the pin.
func checkLibraryFilesPinned(path string, files []string, pin map[string]string) error {
	for _, f := range files {
		key, err := libraryPinKey(f)
		if err != nil {
			return err
		}
		have, err := sha256File(f)
		if err != nil {
			return unsup("stdlib source package %q: cannot hash %s (%v) — fail closed", path, f, err)
		}
		want, ok := pin[key]
		if !ok {
			return unsup("stdlib source file %s is selected for lowering but has NO row in %s — the library pin does not cover it (fail closed; regenerate the pin deliberately with the reason)", key, stdlibPinPath)
		}
		if want != have {
			return unsup("stdlib source file %s DIFFERS from the library pin (%s: pinned %s…, have %s…) — the lowered library text is not the pinned text (fail closed; a re-pin is a deliberate act with a full differential and a written reason)", key, stdlibPinPath, want[:12], have[:12])
		}
	}
	return nil
}

// checkPinnedFilesSelected is the OTHER direction of the pin (audit fix
// round F3: `selected ⊆ pinned` alone let a deleted, unreached-but-import-
// bearing pinned file — strings/reader.go — change the wire with exit 0):
// every pin row under the package's directory must be among the files
// selected for lowering. A pinned file that vanished, or that go/build no
// longer selects, means the lowered package is not the pinned package.
func checkPinnedFilesSelected(path string, files []string, pin map[string]string) error {
	selected := map[string]bool{}
	for _, f := range files {
		key, err := libraryPinKey(f)
		if err != nil {
			return err
		}
		selected[key] = true
	}
	prefix := path + "/"
	missing := []string{}
	for key := range pin {
		if !strings.HasPrefix(key, prefix) || strings.Contains(key[len(prefix):], "/") {
			continue // another package (or a sub-package)
		}
		if !selected[key] {
			missing = append(missing, key)
		}
	}
	if len(missing) > 0 {
		sort.Strings(missing)
		return unsup("stdlib source package %q: pinned file(s) %v are NOT among the files selected for lowering (deleted, renamed, or dropped by the build context) — the lowered package is not the pinned package (fail closed; %s)", path, missing, stdlibPinPath)
	}
	return nil
}

// stdlibPinManifest renders the pin file for the CURRENT source root:
// every selected file of every allowed package with its sha256, sorted,
// under a header naming the rev. This is what baselines/stdlib-pin.tsv
// must equal byte-for-byte modulo the '# generated:' line
// (scripts/check-frontend-pins).
func stdlibPinManifest() (string, error) {
	if err := checkStdlibSrcRev(); err != nil {
		return "", err
	}
	tool, _ := pinnedToolchainName()
	paths := make([]string, 0, len(stdlibSourceAllowed))
	for p := range stdlibSourceAllowed {
		paths = append(paths, p)
	}
	sort.Strings(paths)
	var b strings.Builder
	b.WriteString("# GoLean stdlib LIBRARY PIN — the lowered library text at the oracle pin (" + tool + ").\n")
	b.WriteString("# GENERATED by `GO111MODULE=off go run ./tools/nativefrontend --stdlib-pin-manifest`;\n")
	b.WriteString("# checked by scripts/check-frontend-pins [stdlib-pin] and, at every emit that loads a\n")
	b.WriteString("# library unit, by tools/nativefrontend/stdlibsource.go (checkLibraryFilesPinned).\n")
	b.WriteString("# One row per file the frontend SELECTS for an allowed library package (oracle build\n")
	b.WriteString("# context linux/amd64 + stdlib-substitutions.tsv): path relative to deps/go/src, sha256.\n")
	b.WriteString("# Moves ONLY with a deliberate oracle re-pin, a full differential, and a written reason\n")
	b.WriteString("# (docs/2026-09-03_stdlib-boundary-design.md §2.1.3, G3/G9 ruled 2026-09-03).\n")
	for _, p := range paths {
		files, err := selectLibraryFiles(p)
		if err != nil {
			return "", err
		}
		for _, f := range files {
			key, err := libraryPinKey(f)
			if err != nil {
				return "", err
			}
			sum, err := sha256File(f)
			if err != nil {
				return "", unsup("stdlib pin manifest: cannot hash %s (%v)", f, err)
			}
			b.WriteString(key + "\t" + sum + "\n")
		}
	}
	return b.String(), nil
}

// linknameDirectives scans a parsed file for `//go:linkname local [target]`
// and returns local -> the directive text.
func linknameDirectives(f *ast.File) map[string]string {
	out := map[string]string{}
	for _, group := range f.Comments {
		for _, c := range group.List {
			text := strings.TrimSpace(c.Text)
			if !strings.HasPrefix(text, "//go:linkname ") {
				continue
			}
			fields := strings.Fields(strings.TrimPrefix(text, "//go:linkname "))
			if len(fields) >= 1 {
				out[fields[0]] = text
			}
		}
	}
	return out
}

// parseLibrary loads one allowed library package as a source unit:
// selected files parsed in lexical order (E8), rev + pin checked, the
// linkname directives recorded. The pin map is loaded once per program
// by the loader and passed in.
func (l *loader) parseLibrary(path string, pin map[string]string) (*sourcePkg, error) {
	files, err := selectLibraryFiles(path)
	if err != nil {
		return nil, err
	}
	if err := checkLibraryFilesPinned(path, files, pin); err != nil {
		return nil, err
	}
	if err := checkPinnedFilesSelected(path, files, pin); err != nil {
		return nil, err
	}
	unit := &sourcePkg{path: path, library: true, libFiles: files, linknamed: map[string]string{}}
	pkgName := ""
	for _, f := range files {
		af, err := parser.ParseFile(l.fset, f, nil, parser.ParseComments)
		if err != nil {
			return nil, fmt.Errorf("stdlib source package %q: %w", path, err)
		}
		if pkgName == "" {
			pkgName = af.Name.Name
		} else if af.Name.Name != pkgName {
			return nil, unsup("stdlib source package %q: selected files declare two package names (%s, %s) — file selection is wrong for this pin (fail closed)", path, pkgName, af.Name.Name)
		}
		for local, directive := range linknameDirectives(af) {
			unit.linknamed[local] = directive
		}
		unit.files = append(unit.files, af)
	}
	// NO shim injection into library units: the shims are user-package
	// text (stdlibshim.go); a library body calling a shimmed member
	// (`strconv.baseError` → `errors.New`) resolves to the REAL library
	// function through the qualified-call path, like every other
	// library-to-library call.
	return unit, nil
}
