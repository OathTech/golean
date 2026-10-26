package main

// modfile.go — the module's `go` directive (BUG-109; whole-project review
// 2026-09-11 F2; RULED [USER] Mike 2026-09-11, relayed by the
// [AGENT] coordinator: refuse non-1.26; lane fix/review-boundary-0911).
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
// (already refused as reserved tags by langversion.go). The directive is
// parsed by a small strict scanner — stdlib only, no x/mod — that refuses
// anything it does not understand rather than guess. Since 2026-10-13 (BUG-128, release-
// readiness row 39; RULED [USER] Mike 2026-10-13, item 3 agreed, relayed)
// the same scanner REFUSES a `godebug` line or block BY NAME: the go
// command folds the main module's godebug settings into the binary's
// defaults (cmd/go/internal/load/godebug.go defaultGODEBUG) and the
// model implements the Go 1.26 module defaults only — `panic(nil)`
// raises *runtime.PanicNilError, the differential oracle is pinned with
// GODEBUG=panicnil=0 (scripts/diff-coverage). gc reads only the MAIN
// module's godebug lines; the refusal fires in every go.mod this scanner
// reads (a nested module's too), by name, rather than re-deriving which
// module is main. The source twin `//go:debug` is directives.go.
//
// Since 2026-10-26 (deep-clean review DC06 — FE-03/FE-04; [USER] ruling of
// 2026-10-26, relayed: validate the complete version against the pin,
// refuse what the scanner does not fully validate, keep the Go 1.26
// language policy) the scanner VALIDATES every directive it accepts
// instead of skipping its content: `module` is required, single and takes
// one path; `require`/`exclude` take a module path and a canonical semver
// version; `replace` takes `old [v] => new [v]` with a version-less `new`
// only as a directory path; `retract` a version or a `[lo, hi]` range;
// `tool`/`ignore` one path; a block (`verb (` … `)`) must close before EOF
// and each body line is judged by its verb's rule; a quoted token, a
// `module (` block and any shape outside these rules are refused BY NAME
// as not validated here (over-refusal of an exotic go.mod gc accepts is
// the fail-closed direction; before this, `module` alone, a repeated
// `module`, `require nonsense` and an unterminated block all exported a
// wire gc refuses — measured on go1.26.5). The `go` directive's COMPLETE
// version is compared against the pinned toolchain: a floor above it
// (`go 1.26.6`, `go 1.26.99`) is refused — gc itself refuses to build such
// a module under GOTOOLCHAIN=local («go: go.mod requires go >= 1.26.99»),
// and under GOTOOLCHAIN=auto would switch to a toolchain the semantics is
// not measured against — and a PRERELEASE spelling (`go 1.26rc1`, which gc
// accepts at the pin) is refused by name: the oracle is the release
// go1.26.5, and no prerelease is measured. Every refusal here begins
// `module directive: ` — the negative corpus's frontend leg reads that
// prefix as the `module` rejection class (scripts/coverage-negative), and
// the corpus rows under Corpus/coverage/negative/compile/modules/ pin gc's
// rejection of each shape beside this scanner's.
//
// Since 2026-10-26 (train-19 shake review F1/F2/F5, lane
// frontend/workspace-and-oracle-1026; [USER] ruling of 2026-10-26, relayed:
// fix in the fail-closed direction and keep the admitted surface small —
// the BUG-127/128 rule):
//
//	(1) A WORKSPACE is refused by name (BUG-135). The go command reads
//	    go.work the way it reads go.mod — found by walking up from the
//	    directory (cmd/go/internal/modload/init.go findWorkspaceFile) — and
//	    applies its `go`, `toolchain` and `godebug` lines to the
//	    workspace's modules, so a module whose own go.mod is clean means
//	    something else inside a workspace (measured at go1.26.5: `godebug
//	    panicnil=1` in a go.work beside a `go 1.26` go.mod flips
//	    `recover() == nil` after `panic(nil)` to true; before this change
//	    the frontend exported the program unchanged and the machine
//	    answered false, status ok — a wrong answer with a clean export;
//	    a go.work `go 1.26.6` line makes gc refuse the build outright).
//	    Nothing in a go.work is read here: the lowered directory and
//	    every case-local package are refused when a go.work is in scope
//	    for them (refuseWorkspace). GOWORK is honoured as the go command
//	    honours it (goenv.go, train-20 audit F1/F2, 2026-10-26): from the
//	    process environment when non-empty, else the go env file, else
//	    the toolchain's go.env — `off` disables workspace mode (the
//	    apparatus pins GOWORK=off on its oracle AND frontend legs, so no
//	    workspace above a checkout can move a verdict), empty or `auto`
//	    is the walk, any other value names a workspace file and is
//	    refused by name without reading it (measured: the env file's
//	    GOWORK=off disables a go.work beside the module, its
//	    GOWORK=<path> selects one with no go.work in the walk). In
//	    GOPATH mode (GO111MODULE=off, the positive corpus's mode) the go
//	    command ignores go.work (measured) while this scanner still
//	    refuses one — the same over-refusal as for go.mod, by name.
//	(2) The `toolchain` directive follows gc's own rule plus the pin
//	    (judgeToolchain). gc DROPS a toolchain line that is `default`,
//	    textually equal to `go<goVersion>` or below go1.21
//	    (cmd/go/internal/modload/init.go WriteGoMod) and, under the
//	    default -mod=readonly, refuses to build until go.mod is updated
//	    («updates to go.mod needed; to update it: go mod tidy» — measured
//	    on `go 1.26.5` + `toolchain go1.26.5`, which this scanner EXPORTED
//	    before: an admission false green, review F2); a name outside
//	    gc's `go1…`/`default` grammar is a parse error («invalid toolchain
//	    version 'local': must match format go1.23.0 or default»). Each is
//	    refused by name with gc's reason; a toolchain line is ACCEPTED only
//	    when it names the pinned toolchain and the `go` line is below it
//	    (gc keeps `go 1.26` + `toolchain go1.26.4`, `go 1.26.5` +
//	    `toolchain go1.26.6` and `toolchain go1.27.0` — inert under
//	    GOTOOLCHAIN=local — and those stay refused by the pin policy).
//	(3) An EMPTY block written on one line — `require ()`, `require ( )`,
//	    with a trailing comment — is gc's grammar for every accepted
//	    block verb (measured: each builds) and is accepted; it was
//	    refused with a message that misdescribed it (review F5). A
//	    one-line block WITH a body (`require (a.b/c v1.0.0)`) is refused
//	    as before: gc refuses it too («usage: require module/path
//	    v1.2.3»). `go ()` and `toolchain ()` are gc parse errors
//	    («unknown block type»), `module ()` has no path («missing module
//	    declaration»): refused by name with those reasons.
//	(4) Six shapes gc refuses that the scanner EXPORTED, pre-existing on
//	    main (train-20 pre-merge audit F4, 2026-10-26; the same class as
//	    (2): a wire for a module gc will not build), each measured and
//	    closed by its rule, not its instance: (a) gc's LEXER (x/mod
//	    modfile/read.go) separates tokens with space, tab and CR only and
//	    takes any other printable non-space rune as an identifier byte —
//	    so a NBSP, a form feed, a vertical tab, a NUL or a DEL is
//	    «unexpected input character» — where `strings.Fields` split on
//	    every Unicode space and read `module<NBSP>test` as two words; the
//	    scanner now judges every rune of a line by gc's rule before
//	    splitting, and `{`/`}` are tokens of their own as in gc's lexer,
//	    so `tool foo{bar` has three arguments («tool directive expects
//	    exactly one argument») and `replace a.b/c => ./x{y` fails the
//	    usage rule, both gc's reasons. (b) MAJOR-VERSION AGREEMENT
//	    (module.CheckPathMajor, module.SplitPathVersion): a require,
//	    exclude or versioned replace side whose version's major does not
//	    match its path's suffix («should be v0 or v1, not v2», «should be
//	    v2, not v1»; `/v1`, `/v02` and `/v2.1` suffixes are «malformed
//	    module path»; gopkg.in's `.vN` form included), and a retract
//	    version against the module's own path, are refused with gc's
//	    text. (c) BUILD METADATA: the only canonical form is
//	    `+incompatible`; `v1.0.0+build.1` makes the go command resolve
//	    the version by a module lookup, which the apparatus's GOPROXY=off
//	    refuses («module lookup disabled by GOPROXY=off») and which could
//	    not keep the written version — refused by name. The negative rows
//	    under modules/ pin each shape on gc's side.

import (
	"bufio"
	"errors"
	"go/version"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"unicode"
)

// modRefuse is every refusal of this file: `module directive: ` then the
// cause. The prefix is load-bearing — scripts/coverage-negative's frontend
// leg classes a first line `nativefrontend: native frontend unsupported:
// module directive: …` as the `module` rejection.
func modRefuse(format string, args ...any) error {
	return unsup("module directive: "+format, args...)
}

// findGoMod returns the nearest go.mod at or above dir ("" if none),
// following the go command's module-root search. dir is made absolute
// first so the walk terminates at the filesystem root. A stat error other
// than "does not exist" (a permission denial, an I/O error) is a refusal:
// before 2026-10-26 it read as "no go.mod here" and the walk went on — a
// go.mod the frontend cannot read is not one it may ignore (DC06 local
// space).
func findGoMod(dir string) (string, error) {
	abs, err := filepath.Abs(dir)
	if err != nil {
		return "", modRefuse("cannot resolve %s (%v) — fail closed", dir, err)
	}
	for d := abs; ; d = filepath.Dir(d) {
		candidate := filepath.Join(d, "go.mod")
		fi, err := os.Stat(candidate)
		switch {
		case err == nil && !fi.IsDir():
			return candidate, nil
		case err == nil:
			// A DIRECTORY named go.mod: the go command does not read it
			// as a module file; the walk continues (as it does there).
		case errors.Is(err, fs.ErrNotExist):
		default:
			return "", modRefuse("cannot stat %s (%v) — a go.mod the frontend cannot read is not one it may ignore; fail closed", candidate, err)
		}
		if filepath.Dir(d) == d {
			return "", nil
		}
	}
}

// goModVerbs: what this scanner does with each directive of gc's go.mod
// grammar at the pin (cmd/vendor/golang.org/x/mod/modfile/rule.go, the
// strict parser's verb switch — the go command refuses any other first
// token: «unknown directive: <verb>», measured). x/mod's lexer makes `(`,
// `)`, `[`, `]` and `,` tokens of their own, so `godebug(` is `godebug` `(`
// (measured: gc honours it) and `[v1.0.0,` is `[` `v1.0.0` `,`; the scanner
// splits them off before reading the verb.
//
//	module                 REQUIRED, exactly once, one path (the path names
//	                       nothing the lowering reads: imports are stdlib or
//	                       case-local); `module (` is refused (not validated).
//	go                     JUDGED: exactly once, a release version whose
//	                       language is the pinned one (BUG-109) and whose
//	                       complete version is not above the pinned
//	                       toolchain (DC06); a prerelease is refused.
//	toolchain              exactly once; judged at the end of the scan
//	                       (judgeToolchain): gc's grammar (`go1…` or
//	                       `default`), gc's redundancy rule (`default`,
//	                       equal to the go line, or below go1.21 is DROPPED
//	                       and -mod=readonly refuses the build), then the
//	                       pin — ACCEPTED only as the pinned toolchain's
//	                       name (go1.26.5) above the go line; any other
//	                       name REFUSED: under GOTOOLCHAIN=auto a consumer
//	                       would be switched to a toolchain the semantics
//	                       is not measured against (the apparatus runs
//	                       GOTOOLCHAIN=local, where the line is inert).
//	godebug                REFUSED by name, line or block, with or without
//	                       the blank before `(` (BUG-128).
//	require, exclude       path + canonical semver version, line or block.
//	replace                `old [v] => new [v]`; a version-less new is a
//	                       directory path (rooted, `.` or `..`) — gc's rule.
//	retract                a version or `[lo, hi]`, line or block.
//	tool, ignore           one path each, line or block.
//	anything else          REFUSED by name: gc refuses the go.mod, and
//	                       nothing unknown is guessed here.
//
// The module graph cannot reach the lowered program — its imports are the
// standard library (from the pinned GOROOT) and case-local packages
// (relative paths), neither resolved through requires or replaces — so the
// validation above is of SHAPE (what gc refuses), never of resolution.
var goModAccepted = map[string]bool{"module": true, "require": true, "exclude": true, "replace": true, "retract": true, "tool": true, "ignore": true}

// goModVersionRE is x/mod's GoVersionRE (modfile/rule.go): `1.26`,
// `1.26.5`, `1.26rc1`. Group 5 is the prerelease suffix.
var goModVersionRE = regexp.MustCompile(`^([1-9][0-9]*)\.(0|[1-9][0-9]*)(\.(0|[1-9][0-9]*))?([a-z]+[0-9]+)?$`)

// semverCanonicalRE is a canonical semantic version as go.mod requires one
// (`v1.2.3`, a pseudo-version `v0.0.0-20240101000000-abcdef123456`,
// `v2.0.0+incompatible` — `+incompatible` is the ONE build-metadata form
// module.CanonicalVersion keeps). Shortened forms (`v1.2`, `v1`) are
// refused: gc canonicalizes them only under `go mod tidy`/`go get`, and
// this scanner does not re-derive that. semverWithMetadataRE is the same
// with any build metadata, named so the refusal can say what it is.
var semverCanonicalRE = regexp.MustCompile(`^v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*)?(\+incompatible)?$`)
var semverWithMetadataRE = regexp.MustCompile(`^v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*)?\+[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*$`)

// modulePathElemRE is one element of a module path: the ASCII letters,
// digits and `-._~` of module.CheckPath, not beginning or ending with a
// dot. Narrower than gc (which also refuses Windows reserved names and
// tilde-digit suffixes — over-acceptance of those is a shape gc refuses
// and this scanner does not; recorded) and wider in nothing.
var modulePathElemRE = regexp.MustCompile(`^[A-Za-z0-9_~-]([A-Za-z0-9._~-]*[A-Za-z0-9_~-])?$`)

func modulePathOK(path string) bool {
	if path == "" || strings.HasPrefix(path, "/") || strings.HasSuffix(path, "/") {
		return false
	}
	for _, elem := range strings.Split(path, "/") {
		if !modulePathElemRE.MatchString(elem) {
			return false
		}
	}
	return true
}

// directoryPathOK is gc's rule for a version-less replacement target: a
// rooted path or one starting with `.` or `..` (x/mod modfile/rule.go
// parseReplace: «replacement module without version must be directory path
// (rooted or starting with . or ..)»).
func directoryPathOK(path string) bool {
	return path == "." || path == ".." || strings.HasPrefix(path, "./") || strings.HasPrefix(path, "../") || strings.HasPrefix(path, "/")
}

// lexerRejects judges a line's runes by gc's lexer (x/mod modfile/read.go
// readToken/isIdent): space, tab and CR separate tokens; `(`, `)`, `[`,
// `]`, `{`, `}` and `,` are tokens; a quote opens a string (refused by name
// elsewhere); every other rune must be printable and not a space, else gc
// refuses «unexpected input character». Returns the 1-based byte column of
// the first offending rune, as gc reports it.
func lexerRejects(line string) (col int, r rune, bad bool) {
	for i, r := range line {
		switch r {
		case ' ', '\t', '\r', '(', ')', '[', ']', '{', '}', ',', '"', '`':
			continue
		}
		if unicode.IsSpace(r) || !unicode.IsPrint(r) {
			return i + 1, r, true
		}
	}
	return 0, 0, false
}

// pathMajor mirrors module.SplitPathVersion: the path's major-version suffix
// (`/v2`, gopkg.in's `.v2`) or "", and whether the path is well formed in
// that respect (`/v1`, `/v0`, `/v02`, `/v2.1` are not: «malformed module
// path»).
func pathMajor(path string) (major string, ok bool) {
	if strings.HasPrefix(path, "gopkg.in/") {
		i := len(path)
		if strings.HasSuffix(path, "-unstable") {
			i -= len("-unstable")
		}
		for i > 0 && '0' <= path[i-1] && path[i-1] <= '9' {
			i--
		}
		if i <= 1 || path[i-1] != 'v' || path[i-2] != '.' {
			return "", false
		}
		major = path[i-2:]
		if len(major) <= 2 || major[2] == '0' && major != ".v0" {
			return "", false
		}
		return major, true
	}
	i := len(path)
	dot := false
	for i > 0 && ('0' <= path[i-1] && path[i-1] <= '9' || path[i-1] == '.') {
		if path[i-1] == '.' {
			dot = true
		}
		i--
	}
	if i <= 1 || i == len(path) || path[i-1] != 'v' || path[i-2] != '/' {
		return "", true
	}
	major = path[i-2:]
	if dot || len(major) <= 2 || major[2] == '0' || major == "/v1" {
		return "", false
	}
	return major, true
}

// majorMismatch mirrors module.CheckPathMajor: "" when version v agrees with
// the path's major suffix, else gc's own reason («should be v2, not v1»).
func majorMismatch(v, major string) string {
	if strings.HasPrefix(major, ".v") && strings.HasSuffix(major, "-unstable") {
		major = strings.TrimSuffix(major, "-unstable")
	}
	if strings.HasPrefix(v, "v0.0.0-") && major == ".v1" {
		return ""
	}
	m := v
	if i := strings.IndexAny(v, ".-+"); i >= 0 {
		m = v[:i]
	}
	switch {
	case major == "":
		if m == "v0" || m == "v1" || strings.HasSuffix(v, "+incompatible") {
			return ""
		}
		major = "v0 or v1"
	case major[0] == '/' || major[0] == '.':
		if m == major[1:] {
			return ""
		}
		major = major[1:]
	}
	return "should be " + major + ", not " + m
}

// judgeVersionedPath judges a `path version` pair as gc parses one
// (parseVersion, modulePathMajor, CheckPathMajor): the path's shape and
// major suffix, the version's canonical form, their agreement.
func (m *modScan) judgeVersionedPath(verb, path, v string, lineno int, usage func(string) error, form string) error {
	if !modulePathOK(path) {
		return usage(form)
	}
	major, ok := pathMajor(path)
	if !ok {
		return modRefuse("%s:%d: %s %s: version %q invalid: malformed module path %q — a /vN suffix must be v2 or higher without a leading zero or a dot (module.SplitPathVersion); gc refuses the go.mod the same way; fail closed", m.path, lineno, verb, path, v, path)
	}
	if !semverCanonicalRE.MatchString(v) {
		if semverWithMetadataRE.MatchString(v) {
			return modRefuse("%s:%d: %s %s: version %q is not a canonical module version (build metadata other than +incompatible): the go command resolves such a version by a module lookup, which the apparatus's GOPROXY=off refuses («module lookup disabled by GOPROXY=off») and which could not keep the version as written; fail closed", m.path, lineno, verb, path, v)
		}
		return usage(form)
	}
	if why := majorMismatch(v, major); why != "" {
		return modRefuse("%s:%d: %s %s: version %q invalid: %s — gc refuses the go.mod the same way (module.CheckPathMajor); fail closed", m.path, lineno, verb, path, v, why)
	}
	return nil
}

// modScan is one go.mod being judged.
type modScan struct {
	path      string
	pinnedTC  string
	module    string // the module path, "" until seen
	goVersion string // the `go` directive's version, "" until seen
	toolchain string // the `toolchain` directive's name, "" until seen
	blockVerb string // the open block's verb, "" outside a block
	blockLine int
	retracts  []retractVersion // judged at the end against the module path's major (gc's rule)
}

type retractVersion struct {
	version string
	lineno  int
}

// judgeArgs judges the arguments of an accepted verb — a line's tokens
// after the verb, or a block body line's tokens — by the verb's grammar.
func (m *modScan) judgeArgs(verb string, args []string, lineno int, raw string) error {
	usage := func(form string) error {
		return modRefuse("%s:%d: %q is not `%s` — gc refuses the go.mod («usage: %s»), and the scanner validates every accepted directive's shape rather than skip it; fail closed", m.path, lineno, strings.TrimSpace(raw), form, form)
	}
	for _, a := range args {
		if a == "(" || a == ")" {
			// Not an empty one-line block (goDirective accepts `verb ()`
			// before this): a parenthesis AMONG arguments, or a one-line
			// block with a body (`require (a.b/c v1.0.0)`) — gc refuses
			// both («usage: …»: a block's body begins on the line after
			// `(`, x/mod modfile/read.go); fail closed.
			return modRefuse("%s:%d: %q has a parenthesis among its %s arguments — gc refuses the line too (a block's body begins on the line after `(`); fail closed", m.path, lineno, strings.TrimSpace(raw), verb)
		}
	}
	switch verb {
	case "module":
		if len(args) != 1 || !modulePathOK(args[0]) {
			return usage("module module/path")
		}
	case "require", "exclude":
		if len(args) != 2 {
			return usage(verb + " module/path v1.2.3")
		}
		return m.judgeVersionedPath(verb, args[0], args[1], lineno, usage, verb+" module/path v1.2.3")
	case "tool", "ignore":
		if len(args) != 1 {
			return modRefuse("%s:%d: %q — gc refuses the go.mod («%s directive expects exactly one argument»; `{`, `}`, `[`, `]` and `,` are tokens of their own in its lexer); fail closed", m.path, lineno, strings.TrimSpace(raw), verb)
		}
		if strings.ContainsAny(args[0], "[],{}") {
			return usage(verb + " path")
		}
	case "replace":
		arrow := -1
		for i, a := range args {
			if a == "=>" {
				if arrow >= 0 {
					return usage("replace module/path [v1.2.3] => other/module v1.4\n\t or replace module/path [v1.2.3] => ../local/directory")
				}
				arrow = i
			}
		}
		if arrow < 0 {
			return usage("replace module/path [v1.2.3] => other/module v1.4\n\t or replace module/path [v1.2.3] => ../local/directory")
		}
		left, right := args[:arrow], args[arrow+1:]
		const replaceForm = "replace module/path [v1.2.3] => other/module v1.4\n\t or replace module/path [v1.2.3] => ../local/directory"
		switch len(left) {
		case 1:
			if !modulePathOK(left[0]) {
				return usage(replaceForm)
			}
			if _, ok := pathMajor(left[0]); !ok {
				return modRefuse("%s:%d: replace %s: malformed module path %q — a /vN suffix must be v2 or higher without a leading zero or a dot (module.SplitPathVersion); gc refuses the go.mod the same way; fail closed", m.path, lineno, left[0], left[0])
			}
		case 2:
			if err := m.judgeVersionedPath("replace", left[0], left[1], lineno, usage, replaceForm); err != nil {
				return err
			}
		default:
			return usage(replaceForm)
		}
		switch len(right) {
		case 1:
			if !directoryPathOK(right[0]) {
				return modRefuse("%s:%d: %q — gc refuses the go.mod («replacement module without version must be directory path (rooted or starting with . or ..)»); fail closed", m.path, lineno, strings.TrimSpace(raw))
			}
			if strings.ContainsAny(right[0], "{}[],") {
				return usage(replaceForm)
			}
		case 2:
			if err := m.judgeVersionedPath("replace", right[0], right[1], lineno, usage, replaceForm); err != nil {
				return err
			}
		default:
			return usage(replaceForm)
		}
	case "retract":
		switch {
		case len(args) == 1 && semverCanonicalRE.MatchString(args[0]):
			m.retracts = append(m.retracts, retractVersion{args[0], lineno})
		case len(args) == 5 && args[0] == "[" && args[2] == "," && args[4] == "]" && semverCanonicalRE.MatchString(args[1]) && semverCanonicalRE.MatchString(args[3]):
			m.retracts = append(m.retracts, retractVersion{args[1], lineno}, retractVersion{args[3], lineno})
		default:
			return usage("retract v1.2.3 | retract [v1.2.3, v1.2.5]")
		}
	default:
		return modRefuse("%s:%d: internal: judgeArgs on verb %q — fail closed", m.path, lineno, verb)
	}
	return nil
}

// goDirective scans the go.mod at path, judging every directive by
// goModVerbs, and returns the `go` directive's version as written
// ("1.26.5"). Fail closed: anything the grammar above does not admit is a
// refusal naming the file and the line.
func goDirective(path string) (string, error) {
	f, err := os.Open(path)
	if err != nil {
		return "", modRefuse("cannot read %s (%v) — fail closed", path, err)
	}
	defer f.Close()
	pinnedTC, err := pinnedToolchainName()
	if err != nil {
		return "", err
	}
	m := &modScan{path: path, pinnedTC: pinnedTC}
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 0, 64*1024), 1<<20)
	tokens := strings.NewReplacer("(", " ( ", ")", " ) ", "[", " [ ", "]", " ] ", "{", " { ", "}", " } ", ",", " , ")
	lineno := 0
	for sc.Scan() {
		lineno++
		raw := sc.Text()
		line := raw
		if i := strings.Index(line, "//"); i >= 0 {
			line = line[:i]
		}
		if i := strings.Index(line, "/*"); i >= 0 {
			return "", modRefuse("%s:%d:%d: a /* */ comment — gc refuses the go.mod («mod files must use // comments (not /* */ comments)»); fail closed", path, lineno, i+1)
		}
		if col, r, bad := lexerRejects(line); bad {
			return "", modRefuse("%s:%d:%d: unexpected input character %#q — gc's lexer refuses the go.mod the same way (x/mod modfile/read.go: space, tab and CR separate tokens; an identifier is any printable non-space rune); fail closed", path, lineno, col, r)
		}
		if strings.ContainsAny(line, "\"`") {
			return "", modRefuse("%s:%d: %q carries a quoted token — x/mod's quoted strings are not validated by this scanner; refuse by name (fail closed)", path, lineno, strings.TrimSpace(raw))
		}
		fields := strings.Fields(tokens.Replace(line))
		if len(fields) == 0 {
			continue
		}
		if m.blockVerb != "" {
			if len(fields) == 1 && fields[0] == ")" {
				m.blockVerb = ""
				continue
			}
			if err := m.judgeArgs(m.blockVerb, fields, lineno, raw); err != nil {
				return "", err
			}
			continue
		}
		verb, args := fields[0], fields[1:]
		switch {
		case verb == "godebug":
			return "", modRefuse("%s sets godebug (%s) — GODEBUG settings are not modeled: the semantics is the Go 1.26 module defaults (panic(nil) raises *runtime.PanicNilError; the differential oracle is pinned with GODEBUG=panicnil=0); refuse by name (fail closed)", path, strings.TrimSpace(raw))
		case verb == "go", verb == "toolchain":
			if len(args) >= 1 && args[0] == "(" {
				return "", modRefuse("%s:%d: %q opens a block — gc refuses the go.mod («unknown block type: %s»); fail closed", path, lineno, strings.TrimSpace(line), verb)
			}
			if verb == "toolchain" {
				if len(args) != 1 {
					return "", modRefuse("%s has a malformed toolchain directive %q — fail closed", path, strings.TrimSpace(line))
				}
				if m.toolchain != "" {
					return "", modRefuse("%s repeats the toolchain directive (%s and %s) — the go command refuses this too («repeated toolchain statement»); fail closed", path, m.toolchain, args[0])
				}
				// Judged after the scan (judgeToolchain): gc's rule compares
				// it with the go line, which may follow it.
				m.toolchain = args[0]
				continue
			}
			if len(args) != 1 || !goModVersionRE.MatchString(args[0]) {
				return "", modRefuse("%s has a malformed go directive %q — fail closed", path, strings.TrimSpace(line))
			}
			if m.goVersion != "" {
				return "", modRefuse("%s repeats the go directive (%s and %s) — the go command refuses this too; fail closed", path, m.goVersion, args[0])
			}
			m.goVersion = args[0]
		case verb == "module":
			if len(args) >= 1 && args[0] == "(" {
				return "", modRefuse("%s:%d: a `module (` block is not validated by this scanner (an empty one, `module ()`, gc refuses: «missing module declaration»); write `module <path>` on one line (fail closed)", path, lineno)
			}
			if m.module != "" {
				return "", modRefuse("%s:%d: repeats the module directive (%s and %q) — the go command refuses this too («repeated module statement»); fail closed", path, lineno, m.module, strings.TrimSpace(line))
			}
			if err := m.judgeArgs("module", args, lineno, raw); err != nil {
				return "", err
			}
			m.module = args[0]
		case goModAccepted[verb]:
			if len(args) == 2 && args[0] == "(" && args[1] == ")" {
				// An EMPTY block on one line (`require ()`, `require ( )`):
				// gc's grammar, nothing to validate (review F5, 2026-10-26;
				// measured: every accepted verb builds in this form).
				continue
			}
			if len(args) == 1 && args[0] == "(" {
				m.blockVerb, m.blockLine = verb, lineno
				continue
			}
			if err := m.judgeArgs(verb, args, lineno, raw); err != nil {
				return "", err
			}
		default:
			return "", modRefuse("%s has a directive this scanner does not know (%q) — the go command refuses the go.mod («unknown directive: %s»), and nothing unknown is guessed here; fail closed", path, strings.TrimSpace(line), verb)
		}
	}
	if err := sc.Err(); err != nil {
		return "", modRefuse("cannot scan %s (%v) — fail closed", path, err)
	}
	if m.blockVerb != "" {
		return "", modRefuse("%s: the %s block opened at line %d is not closed before the end of the file — the go command refuses this too («syntax error (unterminated block …)»); fail closed", path, m.blockVerb, m.blockLine)
	}
	if m.module == "" {
		return "", modRefuse("%s has no module directive — the go command refuses this too («missing module declaration»); fail closed", path)
	}
	if m.goVersion == "" {
		return "", modRefuse("%s has no go directive; the go command assumes go 1.16 for such a module — GoLean implements the Go 1.26 language only", path)
	}
	if err := m.judgeToolchain(); err != nil {
		return "", err
	}
	// gc checks a retract version against the MODULE's own path (the
	// `module test/v2` / `retract v1.0.0` shape: «retract test/v2: version
	// "v1.0.0" invalid: should be v2, not v1», measured) once the file is
	// read; the module line may follow the retract.
	major, ok := pathMajor(m.module)
	if ok {
		for _, r := range m.retracts {
			if why := majorMismatch(r.version, major); why != "" {
				return "", modRefuse("%s:%d: retract %s: version %q invalid: %s — gc refuses the go.mod the same way (module.CheckPathMajor against the module path); fail closed", path, r.lineno, m.module, r.version, why)
			}
		}
	}
	return m.goVersion, nil
}

// gcToolchainNameRE is x/mod's ToolchainRE (modfile/rule.go): a toolchain
// line names `default` or a `go1…` version; anything else is gc's parse
// error «invalid toolchain version '…': must match format go1.23.0 or
// default» (measured on `local`, `none`, `go`, `foo1.26.5`).
var gcToolchainNameRE = regexp.MustCompile(`^default$|^go1($|\.)`)

// judgeToolchain judges the `toolchain` directive once the whole file is
// scanned (the go line may follow it): gc's grammar, then gc's redundancy
// rule, then the pin (the header's paragraph (2)). The accepted case —
// the pinned toolchain's name with a `go` line textually below it — is the
// one gc KEEPS and the pin policy admits; refuseForeignModuleVersion's floor
// check (the go line not above the pin) then makes «below» exact: a
// `go 1.26.6` + `toolchain go1.26.5` module is refused there with gc's own
// «requires go >= 1.26.6».
func (m *modScan) judgeToolchain() error {
	t := m.toolchain
	if t == "" {
		return nil
	}
	if !gcToolchainNameRE.MatchString(t) {
		return modRefuse("%s names toolchain %s — gc refuses the go.mod («invalid toolchain version '%s': must match format go1.23.0 or default»); fail closed", m.path, t, t)
	}
	// gc's rule (cmd/go/internal/modload/init.go WriteGoMod): `default`
	// (no version), the go line's own version, or a version below go1.21
	// (gover.GoStrictVersion) is DROPPED from go.mod, and -mod=readonly
	// refuses to build with that update pending. `go1` alone passes the
	// grammar and is below go1.21; go/version reads it.
	switch {
	case t == "default":
		return modRefuse("%s names toolchain default, which gc drops as redundant (the go line decides) and then refuses to build under -mod=readonly («updates to go.mod needed; to update it: go mod tidy»); remove the line; fail closed", m.path)
	case t == "go"+m.goVersion:
		return modRefuse("%s names toolchain %s, the go line's own version (go %s) — gc drops a toolchain line that is not above the go line as redundant and then refuses to build under -mod=readonly («updates to go.mod needed; to update it: go mod tidy»); remove the line, or declare a go version below it; fail closed", m.path, t, m.goVersion)
	case version.IsValid(t) && version.Compare(t, "go1.21") < 0:
		return modRefuse("%s names toolchain %s, below go1.21 (the first toolchain that reads the line) — gc drops it as redundant and then refuses to build under -mod=readonly («updates to go.mod needed; to update it: go mod tidy»); fail closed", m.path, t)
	}
	if t != m.pinnedTC {
		return modRefuse("%s names toolchain %s; the oracle is pinned to %s — under GOTOOLCHAIN=auto a consumer would build with a toolchain the semantics is not measured against (the apparatus runs GOTOOLCHAIN=local, where the line is inert); refuse by name (fail closed)", m.path, t, m.pinnedTC)
	}
	return nil
}

// findGoWork returns the workspace file in scope for dir ("" if none) the
// way the go command finds one (cmd/go/internal/modload/init.go
// findWorkspaceFile): a walk up from dir to the filesystem root, the first
// regular file named go.work. A directory named go.work is not a workspace
// file (the walk continues, as there); a stat error other than "does not
// exist" is a refusal, as in findGoMod. The go command's one special case
// — it does not cross GOROOT — is not mirrored: a lowered directory inside
// a GOROOT is not an input of this frontend (stdlib units come from the
// pinned tree and are not judged here), and a go.work found above one
// would be refused where gc ignores it: the fail-closed direction.
func findGoWork(dir string) (string, error) {
	abs, err := filepath.Abs(dir)
	if err != nil {
		return "", modRefuse("cannot resolve %s (%v) — fail closed", dir, err)
	}
	for d := abs; ; d = filepath.Dir(d) {
		candidate := filepath.Join(d, "go.work")
		fi, err := os.Stat(candidate)
		switch {
		case err == nil && !fi.IsDir():
			return candidate, nil
		case err == nil:
		case errors.Is(err, fs.ErrNotExist):
		default:
			return "", modRefuse("cannot stat %s (%v) — a go.work the frontend cannot read is not one it may ignore; fail closed", candidate, err)
		}
		if filepath.Dir(d) == d {
			return "", nil
		}
	}
}

// refuseWorkspace refuses the export when a Go WORKSPACE is in scope for
// dir (BUG-135; the header's paragraph (1)). GOWORK as the go command reads
// it — cfg.Getenv("GOWORK") in modload.FindGoWork: the process environment
// when non-empty, else the go env file, else the toolchain's go.env
// (goenv.go): `off` disables workspace mode and nothing is looked for;
// empty or `auto` is the walk; any other value names a workspace file —
// relative, missing or a directory, gc refuses to run («invalid GOWORK: not
// an absolute path», «reading go.work: open …: no such file or directory»,
// measured), and an existing one puts dir in a workspace — so it is refused
// by name without reading it.
func refuseWorkspace(dir string) error {
	const what = "the go command applies a go.work's go, toolchain and godebug lines to the workspace's modules (a `godebug panicnil=1` there flips a go 1.26 module's panic(nil) answer while the module's own go.mod is clean — measured) and resolves the module set from its use directives; workspaces are not modeled and nothing in the file is read here"
	switch gowork, source := loadGoEnv().get("GOWORK"); {
	case gowork == "off":
		return nil
	case gowork != "" && gowork != "auto":
		return modRefuse("%s is lowered with GOWORK=%s (from %s), which selects a workspace file — %s; run gc and the frontend with GOWORK=off, or outside the workspace; refuse by name (fail closed)", dir, gowork, source, what)
	}
	workPath, err := findGoWork(dir)
	if err != nil {
		return err
	}
	if workPath == "" {
		return nil
	}
	return modRefuse("%s is inside the workspace %s (go.work is found by walking up from the directory, as go.mod is) — %s; run gc and the frontend with GOWORK=off (the apparatus does), or lower the module outside the workspace; refuse by name (fail closed)", dir, workPath, what)
}

// refuseForeignModuleVersion refuses the export when the module
// containing dir declares a language version other than the pinned one
// (the BUG-109 form: `go.mod declares go 1.21; GoLean implements the Go
// 1.26 language only`), a `go` floor above the pinned toolchain, or a
// prerelease version (DC06, 2026-10-26) — and, first, when a WORKSPACE is
// in scope for dir (refuseWorkspace, BUG-135, 2026-10-26): a go.work
// governs a directory with or without a go.mod of its own (measured: a
// go.work above a module-less directory makes gc refuse «no modules were
// found in the current workspace»).
func refuseForeignModuleVersion(dir string) error {
	if err := refuseWorkspace(dir); err != nil {
		return err
	}
	modPath, err := findGoMod(dir)
	if err != nil {
		return err
	}
	if modPath == "" {
		return nil // no module: the pinned language version, unchanged
	}
	found, err := goDirective(modPath)
	if err != nil {
		return err
	}
	full := "go" + found
	if !version.IsValid(full) {
		return modRefuse("%s declares go %s, which go/version cannot parse — fail closed", modPath, found)
	}
	pinned, err := pinnedLangVersion()
	if err != nil {
		return err
	}
	lang := version.Lang(full)
	if lang != pinned {
		return modRefuse("%s declares go %s; GoLean implements the Go %s language only (the module's language version changes the program's meaning — e.g. the go1.22 per-iteration loop variable); a module declaring another language version is refused — the way out is to declare the pinned version in go.mod", modPath, strings.TrimPrefix(lang, "go"), strings.TrimPrefix(pinned, "go"))
	}
	pinnedTC, err := pinnedToolchainName()
	if err != nil {
		return err
	}
	if sub := goModVersionRE.FindStringSubmatch(found); sub != nil && sub[5] != "" {
		return modRefuse("%s declares go %s, a prerelease version; the oracle is the release %s and no prerelease is measured — refused by name (gc accepts the spelling at the pin; this is the fail-closed direction)", modPath, found, pinnedTC)
	}
	if version.Compare(full, pinnedTC) > 0 {
		return modRefuse("%s requires go >= %s; the oracle is pinned to %s — gc refuses to build this module under GOTOOLCHAIN=local («go: go.mod requires go >= %s (running %s; GOTOOLCHAIN=local)»), and under GOTOOLCHAIN=auto would switch to a toolchain the semantics is not measured against; refuse by name (fail closed)", modPath, found, pinnedTC, found, strings.TrimPrefix(pinnedTC, "go"))
	}
	return nil
}
