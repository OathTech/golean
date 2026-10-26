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
// (already refused as reserved tags by langversion.go) and the
// `toolchain` directive (with GOTOOLCHAIN=local, the oracle pin guard's
// mode, it cannot switch toolchains). The directive is parsed by a small
// strict scanner — stdlib only, no x/mod — that refuses anything it does
// not understand rather than guess. Since 2026-10-13 (BUG-128, release-
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

import (
	"bufio"
	"errors"
	"go/version"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strings"
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
//	toolchain              exactly once; ACCEPTED only when it names the
//	                       pinned toolchain (go1.26.5); any other name
//	                       REFUSED — under GOTOOLCHAIN=auto a consumer would
//	                       be switched to a toolchain the semantics is not
//	                       measured against (the apparatus runs
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
// `v2.0.0+incompatible`). Shortened forms (`v1.2`, `v1`) are refused: gc
// canonicalizes them only under `go mod tidy`/`go get`, and this scanner
// does not re-derive that.
var semverCanonicalRE = regexp.MustCompile(`^v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*)?(\+[0-9A-Za-z-]+(\.[0-9A-Za-z-]+)*)?$`)

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

// modScan is one go.mod being judged.
type modScan struct {
	path      string
	pinnedTC  string
	module    string // the module path, "" until seen
	goVersion string // the `go` directive's version, "" until seen
	toolchain string // the `toolchain` directive's name, "" until seen
	blockVerb string // the open block's verb, "" outside a block
	blockLine int
}

// judgeArgs judges the arguments of an accepted verb — a line's tokens
// after the verb, or a block body line's tokens — by the verb's grammar.
func (m *modScan) judgeArgs(verb string, args []string, lineno int, raw string) error {
	usage := func(form string) error {
		return modRefuse("%s:%d: %q is not `%s` — gc refuses the go.mod («usage: %s»), and the scanner validates every accepted directive's shape rather than skip it; fail closed", m.path, lineno, strings.TrimSpace(raw), form, form)
	}
	for _, a := range args {
		if a == "(" || a == ")" {
			return modRefuse("%s:%d: %q has a parenthesis where a %s argument belongs — fail closed", m.path, lineno, strings.TrimSpace(raw), verb)
		}
	}
	switch verb {
	case "module":
		if len(args) != 1 || !modulePathOK(args[0]) {
			return usage("module module/path")
		}
	case "require", "exclude":
		if len(args) != 2 || !modulePathOK(args[0]) || !semverCanonicalRE.MatchString(args[1]) {
			return usage(verb + " module/path v1.2.3")
		}
	case "tool", "ignore":
		if len(args) != 1 || strings.ContainsAny(args[0], "[],") {
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
		okLeft := (len(left) == 1 && modulePathOK(left[0])) || (len(left) == 2 && modulePathOK(left[0]) && semverCanonicalRE.MatchString(left[1]))
		okRight := false
		switch len(right) {
		case 1:
			if !directoryPathOK(right[0]) {
				return modRefuse("%s:%d: %q — gc refuses the go.mod («replacement module without version must be directory path (rooted or starting with . or ..)»); fail closed", m.path, lineno, strings.TrimSpace(raw))
			}
			okRight = true
		case 2:
			okRight = modulePathOK(right[0]) && semverCanonicalRE.MatchString(right[1])
		}
		if !okLeft || !okRight {
			return usage("replace module/path [v1.2.3] => other/module v1.4\n\t or replace module/path [v1.2.3] => ../local/directory")
		}
	case "retract":
		switch {
		case len(args) == 1 && semverCanonicalRE.MatchString(args[0]):
		case len(args) == 5 && args[0] == "[" && args[2] == "," && args[4] == "]" && semverCanonicalRE.MatchString(args[1]) && semverCanonicalRE.MatchString(args[3]):
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
	tokens := strings.NewReplacer("(", " ( ", ")", " ) ", "[", " [ ", "]", " ] ", ",", " , ")
	lineno := 0
	for sc.Scan() {
		lineno++
		raw := sc.Text()
		line := raw
		if i := strings.Index(line, "//"); i >= 0 {
			line = line[:i]
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
		case verb == "go":
			if len(args) != 1 || !goModVersionRE.MatchString(args[0]) {
				return "", modRefuse("%s has a malformed go directive %q — fail closed", path, strings.TrimSpace(line))
			}
			if m.goVersion != "" {
				return "", modRefuse("%s repeats the go directive (%s and %s) — the go command refuses this too; fail closed", path, m.goVersion, args[0])
			}
			m.goVersion = args[0]
		case verb == "toolchain":
			if len(args) != 1 {
				return "", modRefuse("%s has a malformed toolchain directive %q — fail closed", path, strings.TrimSpace(line))
			}
			if m.toolchain != "" {
				return "", modRefuse("%s repeats the toolchain directive (%s and %s) — the go command refuses this too («repeated toolchain statement»); fail closed", path, m.toolchain, args[0])
			}
			m.toolchain = args[0]
			if args[0] != pinnedTC {
				return "", modRefuse("%s names toolchain %s; the oracle is pinned to %s — under GOTOOLCHAIN=auto a consumer would build with a toolchain the semantics is not measured against (the apparatus runs GOTOOLCHAIN=local, where the line is inert); refuse by name (fail closed)", path, args[0], pinnedTC)
			}
		case verb == "module":
			if len(args) == 1 && args[0] == "(" {
				return "", modRefuse("%s:%d: a `module (` block is not validated by this scanner; write `module <path>` on one line (fail closed)", path, lineno)
			}
			if m.module != "" {
				return "", modRefuse("%s:%d: repeats the module directive (%s and %q) — the go command refuses this too («repeated module statement»); fail closed", path, lineno, m.module, strings.TrimSpace(line))
			}
			if err := m.judgeArgs("module", args, lineno, raw); err != nil {
				return "", err
			}
			m.module = args[0]
		case goModAccepted[verb]:
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
	return m.goVersion, nil
}

// refuseForeignModuleVersion refuses the export when the module
// containing dir declares a language version other than the pinned one
// (the BUG-109 form: `go.mod declares go 1.21; GoLean implements the Go
// 1.26 language only`), a `go` floor above the pinned toolchain, or a
// prerelease version (DC06, 2026-10-26).
func refuseForeignModuleVersion(dir string) error {
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
