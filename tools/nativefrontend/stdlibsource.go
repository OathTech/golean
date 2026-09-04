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
//     reading it refuses instead of yielding a zero-valued cell (the
//     silent-wrong-answer shape: math/bits' `overflowError`).
//   - Anything outside the allowed list keeps today's refusals verbatim.

import (
	"crypto/sha256"
	_ "embed"
	"encoding/hex"
	"fmt"
	"go/ast"
	"go/build"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
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
	"strings":              "slice-1 target (Fields, TrimSpace, Split retired from shims); slice 2: Join, Repeat and the Builder TYPE retired from shim/shadow model — Builder's three unsafe sites (String, copyCheck's NoEscape, grow's MakeNoZero) are OVERLAID (stdlib-overlay.tsv); pure Go at function granularity given the bytealg substitution",
	"strconv":              "slice-1 target (FormatUint, FormatInt, ParseUint retired from shims); thin wrappers over internal/strconv; the Parse* ERROR paths reach internal/stringslite.Clone, OVERLAID in slice 2 (BUG-089's nine designed reds closed)",
	"internal/strconv":     "strconv's implementation package; pure Go except deps.go's four float-bits casts — a bit reinterpretation the language has no operation for and the machine has no op for (a PRIMITIVE admission, [USER]-gated; NOT overlaid in slice 2): FormatFloat/ParseFloat/AppendFloat quarantine by name (FR-21 row stdlib-source/frontier/format-float-unsafe)",
	"internal/stringslite": "strings/strconv's shared Index/Cut/Clone helpers; Clone's unsafe.String is OVERLAID to string(b) (slice 2, byte-checked)",
	"internal/bytealg":     "the byte-search leaves strings.Index/Count/Split reach; assembly on amd64, swapped for the package's own *_generic.go twins by stdlib-substitutions.tsv; MakeNoZero (body-less) is overlaid away at its one strings caller",
	"unicode":              "unicode.IsSpace and its White_Space RangeTable (strings.Fields/TrimSpace's non-ASCII path); pure tables, reached ones only",
	"unicode/utf8":         "rune decoding used by strings' non-ASCII paths and explode; pure",
	"math/bits":            "internal/strconv's formatBits uses bits.TrailingZeros, strings.Repeat uses bits.Mul, slices uses bits.Len; pure except the two runtime-linknamed error VALUES (poisoned by the linkname rule)",
	"errors":               "errors.New (slice 2: the user-facing SHIM retired — every errors.New is the real *errors.errorString), Join (its unsafe.String OVERLAID), Unwrap; Is/As reach internal/reflectlite and refuse by name (FR-21 → G6)",
	"bytes":                "slice-2 target (Equal retired from shim; Buffer retired from the E5-T shadow model — pure Go, its growth idiom `append([]byte(nil), make([]byte, c)...)` is the overlay's model); ReadFrom/WriteTo reach `io` (export data only) and quarantine by name; init-pure: three errors.New sentinels + the asciiSpace table",
	"slices":               "slice-2 target (SortFunc retired from the generic desugar — pdqsortCmpFunc stenciled per element type by mono.go, gc's exact member incl. tie order); Sort stays the sortSlice MACHINE OP at integer kinds until memo §3 row M (frontendInterceptedLibraryMembers); Insert/Replace reach `overlaps` (unsafe.Sizeof/pointer arithmetic) and refuse by name — REFUSED, not overlaid (FR-21 row stdlib-source/frontier/slices-overlaps); iter-typed members are unreached unless called; init-pure: no package-level initializers",
	"cmp":                  "slice-2 target (Compare retired from the kind-dispatch desugar — the real generic body, NaN arm included, so floats lower too); pure, no imports; init-pure: no package-level state",
	"encoding/binary":      "slice-2 target (LittleEndian.Uint64/PutUint64 retired from the package-variable method desugar — the exported vars and their unexported receiver types lower as ordinary library declarations); Read/Write/Size are reflect and refuse by name (export data); init-pure: two errors.New sentinels, zero-valued ByteOrder vars, a sync.Map (structSize, dataSize's cache) reached whenever Write/Read/Size is — its TYPE does not lower, so the var is POISONED per declaration (`$poisoned` cell; dataSize and every reader an H-3 stub naming the var, its type and the cause — ledger FR-24, PARTIALLY CLOSED 2026-09-04, lane fr24; the init-pure claim itself holds: the var has no initializer)",
}

//go:embed stdlib-substitutions.tsv
var stdlibSubstitutionsTSV string

// ---- the OVERLAY table (stdlib source-through slice 2, 2026-09-03) ----
//
// An overlay substitutes ONE pure-Go expression for ONE unsafe (or
// runtime-implemented) expression at ONE named site of the pinned source
// (memo §2.3.2 item 3). It is the only hand-written library text the
// frontend carries — governed by the admission register's cap (12 `expr`
// rows, stdlibregister.go) and BYTE-CHECKED at every load: the recorded
// line of the pinned file must carry the `old` bytes exactly once, or the
// unit refuses by name. The library pin hashes the UPSTREAM bytes; the
// overlay is applied to the in-memory copy AFTER the pin check, so a
// re-pin that moves an overlaid line fails both. The table is the SINGLE
// source for the applied substitutions and for the register's overlay
// rows (audit fix round F12's owed assertion: nothing the emitter applies
// can be outside the register, because both read this file; and
// `--stdlib-overlay-check` re-verifies every row against the checkout so
// scripts/check-stdlib-register catches a stale row without a program).

//go:embed stdlib-overlay.tsv
var stdlibOverlayTSV string

// stdlibOverlayRow is one row of stdlib-overlay.tsv.
type stdlibOverlayRow struct {
	pkg, file string
	line      int
	kind      string // "expr" (counted) | "import" (consequential, uncounted)
	old, new  string
	reason    string
}

// site renders "<pkg>/<file>:<line>" — the register's entry column and
// every refusal's name for the row.
func (r stdlibOverlayRow) site() string {
	return r.pkg + "/" + r.file + ":" + itoa(r.line)
}

// parseStdlibOverlay parses the embedded table. Every malformation, and
// every rule the header states, refuses at first use — never a skipped
// line, never a row applied outside the rules.
func parseStdlibOverlay(tsv string) ([]stdlibOverlayRow, error) {
	var rows []stdlibOverlayRow
	exprFiles := map[string]bool{}
	seen := map[string]bool{}
	for n, line := range strings.Split(tsv, "\n") {
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		cols := strings.Split(line, "\t")
		if len(cols) != 7 {
			return nil, unsup("stdlib-overlay.tsv line %d is malformed (want package<TAB>file<TAB>line<TAB>kind<TAB>old<TAB>new<TAB>reason, 7 columns; got %d): %q", n+1, len(cols), line)
		}
		for i, c := range cols {
			if c == "" {
				return nil, unsup("stdlib-overlay.tsv line %d: column %d is empty (every column is mandatory)", n+1, i+1)
			}
		}
		ln := 0
		for _, ch := range cols[2] {
			if ch < '0' || ch > '9' {
				return nil, unsup("stdlib-overlay.tsv line %d: line column %q is not a positive integer", n+1, cols[2])
			}
			ln = ln*10 + int(ch-'0')
		}
		if ln == 0 {
			return nil, unsup("stdlib-overlay.tsv line %d: line column must be >= 1", n+1)
		}
		r := stdlibOverlayRow{pkg: cols[0], file: cols[1], line: ln, kind: cols[3], old: cols[4], new: cols[5], reason: cols[6]}
		if _, allowed := stdlibSourceAllowed[r.pkg]; !allowed {
			return nil, unsup("stdlib-overlay.tsv line %d: package %q is not on the allowed-library list — an overlay into a package that is not source-through is meaningless (fail closed)", n+1, r.pkg)
		}
		if strings.Contains(r.file, "/") || filepath.Ext(r.file) != ".go" {
			return nil, unsup("stdlib-overlay.tsv line %d: file %q must be a bare .go file name inside the package directory", n+1, r.file)
		}
		switch r.kind {
		case "expr":
			for _, banned := range []string{"unsafe", "abi.", "bytealg."} {
				if strings.Contains(r.new, banned) {
					return nil, unsup("stdlib-overlay.tsv line %d (%s): the substitute %q mentions %q — an overlay may not reintroduce what it removes (fail closed)", n+1, r.site(), r.new, banned)
				}
			}
			exprFiles[r.pkg+"/"+r.file] = true
		case "import":
			if !strings.HasPrefix(r.old, `"`) || !strings.HasSuffix(r.old, `"`) || r.new != "_ "+r.old {
				return nil, unsup("stdlib-overlay.tsv line %d (%s): an import row must neutralize exactly one import spec (old %q -> new `_ %s`); got new %q", n+1, r.site(), r.old, r.old, r.new)
			}
		default:
			return nil, unsup("stdlib-overlay.tsv line %d (%s): kind %q is not one of expr, import", n+1, r.site(), r.kind)
		}
		if r.old == r.new {
			return nil, unsup("stdlib-overlay.tsv line %d (%s): old and new are identical — not a substitution", n+1, r.site())
		}
		if seen[r.site()] {
			return nil, unsup("stdlib-overlay.tsv line %d: duplicate site %s (one row per line)", n+1, r.site())
		}
		seen[r.site()] = true
		rows = append(rows, r)
	}
	for _, r := range rows {
		if r.kind == "import" && !exprFiles[r.pkg+"/"+r.file] {
			return nil, unsup("stdlib-overlay.tsv: import row %s neutralizes an import in a file with no expr row — an import neutralization is admitted only as the consequence of a site in the same file (fail closed)", r.site())
		}
	}
	return rows, nil
}

// stdlibOverlayCount is the number of rows counted against the cap
// (`expr`) and the number of consequential `import` rows.
func stdlibOverlayCount(rows []stdlibOverlayRow) (expr, imports int) {
	for _, r := range rows {
		if r.kind == "expr" {
			expr++
		} else {
			imports++
		}
	}
	return
}

// applyStdlibOverlay applies every row of the table that names this
// library file (pkg + bare file name) to src, returning the overlaid
// bytes and the sites applied. Each row's line must contain `old`
// EXACTLY ONCE (zero: the text moved or the pin changed; more than one:
// the row is ambiguous) — both refuse by site. Substitutions are line-
// local, so line numbers stay upstream's for every later row and for
// every position the frontend reports.
func applyStdlibOverlay(rows []stdlibOverlayRow, pkg, file string, src []byte) ([]byte, []string, error) {
	base := filepath.Base(file)
	var lines [][]byte
	split := false
	applied := []string{}
	var importLines map[int]bool
	for _, r := range rows {
		if r.pkg != pkg || r.file != base {
			continue
		}
		if !split {
			lines = strings_SplitLinesKeepEnds(src)
			split = true
			var err error
			if importLines, err = importDeclLines(file, src); err != nil {
				return nil, nil, err
			}
		}
		// Audit fix round F2: an `expr` row may not target an import line
		// (it could rebind `"internal/bytealg"` under another name and
		// slip past the textual substitute ban); only `import` rows touch
		// the import declaration, and those are shape-checked at parse.
		if r.kind == "expr" && importLines[r.line] {
			return nil, nil, unsup("stdlib overlay %s: an expr row targets a line inside the file's import declaration — only `import` rows (\"p\" -> _ \"p\") may touch imports (fail closed)", r.site())
		}
		if r.line > len(lines) {
			return nil, nil, unsup("stdlib overlay %s: the pinned file has only %d line(s) — the recorded site does not exist in this text (fail closed; the overlay table is stale for this pin)", r.site(), len(lines))
		}
		cur := lines[r.line-1]
		switch n := strings.Count(string(cur), r.old); n {
		case 1:
		case 0:
			return nil, nil, unsup("stdlib overlay %s: the recorded bytes %q are NOT on that line of the pinned file (have %q) — the text under the overlay moved; refusing rather than substituting elsewhere (fail closed; re-derive the row deliberately)", r.site(), r.old, strings.TrimRight(string(cur), "\n"))
		default:
			return nil, nil, unsup("stdlib overlay %s: the recorded bytes %q occur %d times on that line — the row is ambiguous (fail closed)", r.site(), r.old, n)
		}
		lines[r.line-1] = []byte(strings.Replace(string(cur), r.old, r.new, 1))
		applied = append(applied, r.site())
	}
	if !split {
		return src, nil, nil
	}
	out := make([]byte, 0, len(src))
	for _, l := range lines {
		out = append(out, l...)
	}
	// Audit fix round F2, the POST-HOC half: whatever the rows did, the
	// overlaid file may keep NO live binding to `unsafe` or `internal/abi`
	// (the out-of-language packages an overlay exists to remove), nor to
	// any package one of ITS import rows neutralized (a second, live
	// import of the same path would re-open it) — re-derived from the
	// overlaid text's import declaration, refused by file and line.
	// (`internal/bytealg` is a source-through package a file may use
	// legitimately — internal/stringslite does — so it is banned only
	// where an import row of the file neutralized it.)
	banned := map[string]bool{"unsafe": true, "internal/abi": true}
	for _, r := range rows {
		if r.pkg == pkg && r.file == base && r.kind == "import" {
			banned[strings.Trim(r.old, `"`)] = true
		}
	}
	if err := checkNoLiveOverlayBannedImport(file, out, banned); err != nil {
		return nil, nil, err
	}
	return out, applied, nil
}

// importDeclLines returns the set of 1-based line numbers covered by the
// file's import declarations (AST-computed from the UPSTREAM bytes).
func importDeclLines(file string, src []byte) (map[int]bool, error) {
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, file, src, parser.ImportsOnly)
	if err != nil {
		return nil, unsup("stdlib overlay: cannot parse %s to locate its import declaration (%v) — fail closed", file, err)
	}
	lines := map[int]bool{}
	for _, d := range af.Decls {
		gd, ok := d.(*ast.GenDecl)
		if !ok || gd.Tok != token.IMPORT {
			continue
		}
		from, to := fset.Position(gd.Pos()).Line, fset.Position(gd.End()).Line
		for l := from; l <= to; l++ {
			lines[l] = true
		}
	}
	return lines, nil
}

// checkNoLiveOverlayBannedImport parses the OVERLAID text's imports and
// refuses a non-blank binding to an overlayBannedImportPaths package.
func checkNoLiveOverlayBannedImport(file string, overlaid []byte, banned map[string]bool) error {
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, file, overlaid, parser.ImportsOnly)
	if err != nil {
		return unsup("stdlib overlay: the overlaid %s does not parse (%v) — fail closed", file, err)
	}
	for _, imp := range af.Imports {
		path := strings.Trim(imp.Path.Value, `"`)
		if !banned[path] {
			continue
		}
		if imp.Name == nil || imp.Name.Name != "_" {
			return unsup("stdlib overlay: %s:%d keeps a LIVE import of %q after the overlay applied — every use of it must be substituted and the import neutralized (`_ %q`); fail closed", file, fset.Position(imp.Pos()).Line, path, path)
		}
	}
	return nil
}

// typeCheckOverlaidPackage (audit fix round F3): the invariant licensing
// an `import` row — no `p.` selector survives its file's expr rows — is
// enforced by TYPE-CHECKING the overlaid package with go/types (unmodeled
// imports from the host toolchain's export data, which the frontend pins
// to the oracle rev). Any error refuses, naming file and line. Called by
// --stdlib-overlay-check for every package the table names.
func typeCheckOverlaidPackage(pkg string, files []string, rows []stdlibOverlayRow) error {
	fset := token.NewFileSet()
	var parsed []*ast.File
	for _, f := range files {
		src, err := os.ReadFile(f)
		if err != nil {
			return unsup("stdlib overlay check: cannot read %s (%v)", f, err)
		}
		src, _, err = applyStdlibOverlay(rows, pkg, f, src)
		if err != nil {
			return err
		}
		af, err := parser.ParseFile(fset, f, src, parser.ParseComments)
		if err != nil {
			return unsup("stdlib overlay check: overlaid %s does not parse: %v", f, err)
		}
		parsed = append(parsed, af)
	}
	lang, err := pinnedLangVersion()
	if err != nil {
		return err
	}
	var first error
	conf := types.Config{Importer: importer.Default(), GoVersion: lang, Error: func(e error) {
		if first == nil {
			first = e
		}
	}}
	_, err = conf.Check(pkg, fset, parsed, nil)
	if err != nil {
		if first != nil {
			err = first
		}
		return unsup("stdlib overlay check: the overlaid package %q does not type-check — %v (an import row whose file still uses the package, or an expr substitute that does not type; fail closed)", pkg, err)
	}
	return nil
}

// strings_SplitLinesKeepEnds splits src after every '\n', keeping the
// terminator on each piece, so joining the pieces reproduces src byte
// for byte.
func strings_SplitLinesKeepEnds(src []byte) [][]byte {
	var lines [][]byte
	start := 0
	for i, c := range src {
		if c == '\n' {
			lines = append(lines, src[start:i+1])
			start = i + 1
		}
	}
	if start < len(src) {
		lines = append(lines, src[start:])
	}
	return lines
}

// stdlibOverlayCheck verifies EVERY row of the overlay table against the
// pinned checkout with no program in hand (`--stdlib-overlay-check`, run
// by scripts/check-stdlib-register): the row's file must be among the
// files selected for its package, pinned, and carry the recorded bytes
// exactly once at the recorded line. Returns the applied-site report.
func stdlibOverlayCheck() (string, error) {
	if err := checkStdlibSrcRev(); err != nil {
		return "", err
	}
	rows, err := parseStdlibOverlay(stdlibOverlayTSV)
	if err != nil {
		return "", err
	}
	pin, err := loadStdlibPin()
	if err != nil {
		return "", err
	}
	var b strings.Builder
	byPkg := map[string][]string{}
	for _, r := range rows {
		byPkg[r.pkg] = append(byPkg[r.pkg], r.file)
	}
	for _, pkg := range sortedStringKeys(byPkg) {
		files, err := selectLibraryFiles(pkg)
		if err != nil {
			return "", err
		}
		if err := checkLibraryFilesPinned(pkg, files, pin); err != nil {
			return "", err
		}
		selected := map[string]string{}
		for _, f := range files {
			selected[filepath.Base(f)] = f
		}
		// All of a file's rows apply TOGETHER (the byte check is per row
		// inside applyStdlibOverlay; the post-hoc import-binding check
		// needs the whole file's rows in force).
		files_ := map[string]bool{}
		for _, r := range rows {
			if r.pkg == pkg {
				files_[r.file] = true
			}
		}
		for _, file := range sortedStringKeys(files_) {
			f, ok := selected[file]
			if !ok {
				return "", unsup("stdlib overlay %s/%s: the file is not among the files selected for package %q under the oracle context — the row names text the frontend never lowers (fail closed)", pkg, file, pkg)
			}
			src, err := os.ReadFile(f)
			if err != nil {
				return "", unsup("stdlib overlay %s/%s: cannot read %s (%v)", pkg, file, f, err)
			}
			want := 0
			for _, r := range rows {
				if r.pkg == pkg && r.file == file {
					want++
				}
			}
			_, applied, err := applyStdlibOverlay(rows, pkg, f, src)
			if err != nil {
				return "", err
			}
			if len(applied) != want {
				return "", unsup("internal: stdlib overlay %s/%s: %d row(s) applied, %d listed", pkg, file, len(applied), want)
			}
			for _, r := range rows {
				if r.pkg == pkg && r.file == file {
					b.WriteString(r.kind + "\t" + r.site() + "\t" + r.old + " -> " + r.new + "\n")
				}
			}
		}
		if err := typeCheckOverlaidPackage(pkg, files, rows); err != nil {
			return "", err
		}
		b.WriteString("# " + pkg + ": overlaid package type-checks\n")
	}
	expr, imports := stdlibOverlayCount(rows)
	b.WriteString(fmt.Sprintf("# %d expr row(s) (cap %d), %d import row(s) (cap %d): every row's bytes verified at the pinned checkout; every overlaid package type-checked\n", expr, stdlibOverlayCap, imports, stdlibOverlayImportCap))
	return b.String(), nil
}

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
	overlay, err := parseStdlibOverlay(stdlibOverlayTSV)
	if err != nil {
		return nil, err
	}
	unit := &sourcePkg{path: path, library: true, libFiles: files, linknamed: map[string]string{}}
	pkgName := ""
	for _, f := range files {
		// The OVERLAY (stdlib-overlay.tsv) is applied to the in-memory
		// copy AFTER the pin check above hashed the upstream bytes: each
		// row's line must carry its recorded bytes exactly once, or the
		// unit refuses by site. The parser sees the overlaid text under
		// the upstream file name, so every position it reports is the
		// upstream line.
		src, err := os.ReadFile(f)
		if err != nil {
			return nil, unsup("stdlib source package %q: cannot read %s (%v) — fail closed", path, f, err)
		}
		src, applied, err := applyStdlibOverlay(overlay, path, f, src)
		if err != nil {
			return nil, err
		}
		unit.overlaid = append(unit.overlaid, applied...)
		af, err := parser.ParseFile(l.fset, f, src, parser.ParseComments)
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
	// Audit fix round F6: a row naming a file the package does not select
	// would be a silent no-op — every row of this package must have applied
	// exactly once.
	seen := map[string]int{}
	for _, site := range unit.overlaid {
		seen[site]++
	}
	for _, r := range overlay {
		if r.pkg != path {
			continue
		}
		if n := seen[r.site()]; n != 1 {
			return nil, unsup("stdlib overlay %s: the row applied %d time(s) while loading package %q — its file is not among the selected files (or the site is duplicated); a row that does not apply is not an overlay (fail closed)", r.site(), n, path)
		}
	}
	// NO shim injection into library units: the shims are user-package
	// text (stdlibshim.go); a library body calling a shimmed member
	// (`strconv.baseError` → `errors.New`) resolves to the REAL library
	// function through the qualified-call path, like every other
	// library-to-library call.
	return unit, nil
}
