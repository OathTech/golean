package main

// directives.go — COMPILER DIRECTIVES in user units (release-readiness
// rows 38 and 39; the Codex zero-context pass F2/F3,
// docs/2026-10-13_codex-zero-context-pass.md; BUG-127, BUG-128; RULED
// [USER] Mike 2026-10-13, relayed by the [AGENT] coordinator: item 3
// agreed — refuse by name, at file selection, every user unit; and
// the standing preference, Mike 2026-10-13 on BUG-125: refuse the case
// rather than open the door to special-casing, support may come later
// (release-readiness rows 38, 39, 41); lane
// frontend/directives-1013, [AGENT]).
//
// Before this file a `//go:embed data.txt` string was exported and
// answered as the zero value (`len(x) == 0` where gc prints 5), and still
// exported when data.txt was ABSENT and gc rejects the package; a user
// `//go:linkname x runtime.zerobase` variable was answered 0 where gc's
// linker rejects the program; `//go:debug panicnil=1` flipped gc's
// answer (`recover() == nil` true) while the model kept the modern
// semantics (false), and an unknown setting gc rejects was accepted. A
// directive is meaning gc reads from a COMMENT: go/types accepts the
// program, the lowering never sees the comment, and the wrong answer
// ships with a clean export. No directive is modeled; the ones with no
// effect on the compiled program are allowed by name — IN THE PLACEMENTS
// gc accepts them — and every other one REFUSES the export at file
// selection, in the root package and in every case-local imported
// package alike (both go through selectPackageFiles).
//
// gc's recognition rule (cmd/compile/internal/syntax/parser.go, the
// pragma handler; scanner.go lineComment/fullComment): a LINE comment
// whose text begins `go:` is a directive in ANY column — the verb runs to
// the first blank; a BLOCK comment `/*go:…*/` is never handed to the
// pragma handler (only `/*line` is), so it is prose to gc (measured:
// `/*go:embed data.txt*/` leaves the variable empty) and is prose here. A
// verb gc does not know is IGNORED outside the standard library
// (noder.go: the «not allowed» error is std-only), so refusing an unknown
// verb is over-refusal in the fail-closed direction, as ruled.
// PLACEMENT (noder.go pragma / checkUnusedDuringParse; lex.go
// pragmaFlag; the fix round of the lane's review, HIGH-1): gc rejects
// with «misplaced compiler directive» (a) any `//go:` directive, whatever
// its verb, that is not on a line by itself (the scanner's `blank` flag:
// only whitespace before the comment on its line); (b) a `//go:build`
// after the package clause (its flag GoBuildPragma is consumed by the
// package clause only); (c) a `//go:noinline` not consumed by the next
// func or method declaration — before the package clause, inside a
// declaration or a body, before a var/type/const/import declaration, or
// at the end of the file. `//go:generate` carries no flag and is never
// misplaced on its own line. The allowlisted verbs are judged by exactly
// those rules; measured at go1.26.5 on the reviewer's probes a1–a12 and
// the lane's a13–a20 (TestCompilerDirectives pins every shape).
// `//line ` is a line directive at column 1 only; `/*line ` anywhere.
// Both line forms are refused WHEREVER they appear (an indented `//line`
// is prose to gc; refusing it over-refuses by name rather than
// re-implementing the column rule). `//go:debug` is read by the go
// command, not the compiler (cmd/go/internal/load/godebug.go), from the
// files of package main before the package clause; it is refused in any
// package at any position — the runtime-settings contract is the model's
// (docs/cli.md §1; the go.mod `godebug` twin is modfile.go).

import (
	"fmt"
	"go/ast"
	"go/token"
	"os"
	"path/filepath"
	"strings"
)

// allowedDirectiveVerbs is THE ALLOWLIST ([AGENT] proposal ratified by
// the [USER] 2026-10-13, item 3): verb -> why it has no effect on the modeled
// program, in the placements gc accepts. Widening it is a ruling, not an
// edit.
var allowedDirectiveVerbs = map[string]string{
	"go:build":    "a build constraint before the package clause — judged by the langversion.go policy (reserved tags refuse, a custom tag must be inert)",
	"go:noinline": "an inlining hint on the next func or method declaration: optimisation only, no semantic effect (ten corpus files carry it)",
	"go:generate": "a command line for `go generate`, never read by the compiler",
}

// allowedDirectiveList is the allowlist as the refusal text states it.
const allowedDirectiveList = "//go:build, //go:noinline, //go:generate"

// refuseCompilerDirectives scans every comment of the SELECTED files for
// a directive and refuses the first one outside the allowlist, or an
// allowlisted one in a placement gc rejects, naming the directive, the
// file and the position. Called from selectPackageFiles, so the root
// package and every imported local unit are covered by the one site.
func refuseCompilerDirectives(fset *token.FileSet, dir string, files []*ast.File) error {
	for _, f := range files {
		s := &directiveScan{fset: fset, dir: dir, f: f}
		for _, group := range f.Comments {
			for _, c := range group.List {
				if err := s.judge(c); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

// directiveScan is one file's context: the file's bytes are read once,
// lazily, for the own-line rule.
type directiveScan struct {
	fset *token.FileSet
	dir  string
	f    *ast.File
	src  []byte
}

// directiveBody is gc's commentText: the comment without its `//` or its
// `/*` and `*/`, and without a trailing `\r`.
func directiveBody(text string) string {
	if strings.HasPrefix(text, "/*") {
		return strings.TrimSuffix(text[2:], "*/")
	}
	return strings.TrimSuffix(strings.TrimPrefix(text, "//"), "\r")
}

// directiveVerb returns the `go:verb` of a directive body (the text up to
// the first blank), "" when the body is not a go: directive.
func directiveVerb(body string) string {
	if !strings.HasPrefix(body, "go:") {
		return ""
	}
	if i := strings.IndexAny(body, " \t"); i >= 0 {
		return body[:i]
	}
	return body
}

// firstLine is the directive as the refusal quotes it: its first line
// (a block comment may span several), trailing blanks trimmed.
func firstLine(text string) string {
	if i := strings.IndexByte(text, '\n'); i >= 0 {
		text = text[:i]
	}
	return strings.TrimRight(text, " \t\r")
}

func (s *directiveScan) judge(c *ast.Comment) error {
	body := directiveBody(c.Text)
	switch {
	case strings.HasPrefix(body, "line "):
		return unsup("file selection in %s: %s carries the line directive `%s` — position rewriting is not modeled (gc honours //line at column 1 and /*line anywhere; both forms are refused wherever they appear); refuse by name (fail closed)", s.dir, s.pos(c), firstLine(c.Text))
	case strings.HasPrefix(c.Text, "/*"):
		// A block `/*go:…*/` comment is prose to gc (scanner.go
		// fullComment hands only `line` block comments to the pragma
		// handler): not a directive, nothing to refuse.
		return nil
	case strings.HasPrefix(body, "go:"):
		verb := directiveVerb(body)
		if verb == "go:debug" {
			return unsup("file selection in %s: %s carries the runtime-setting directive `%s` — GODEBUG settings are not modeled: the semantics is the Go 1.26 module defaults (panic(nil) raises *runtime.PanicNilError; the differential oracle is pinned with GODEBUG=panicnil=0); refuse by name (fail closed)", s.dir, s.pos(c), firstLine(c.Text))
		}
		if _, ok := allowedDirectiveVerbs[verb]; !ok {
			return unsup("file selection in %s: %s carries the compiler directive `%s` — a //go: directive outside the allowlist (%s) is not modeled (gc may embed data, rename a symbol or change code generation on it, or ignore it; none of that is modeled); refuse by name, no modelling (fail closed)", s.dir, s.pos(c), firstLine(c.Text), allowedDirectiveList)
		}
		return s.judgePlacement(c, verb)
	}
	return nil
}

// judgePlacement applies gc's placement rules to an allowlisted
// directive: the three «misplaced compiler directive» shapes gc rejects
// are refused by name, so that an allowlisted verb never admits a
// program gc refuses.
func (s *directiveScan) judgePlacement(c *ast.Comment, verb string) error {
	own, err := s.ownLine(c)
	if err != nil {
		return err
	}
	if !own {
		return unsup("file selection in %s: %s carries the compiler directive `%s` after code on the same line — gc rejects it («misplaced compiler directive»: a directive must be on a line by itself, whatever its verb); refused by name (fail closed)", s.dir, s.pos(c), firstLine(c.Text))
	}
	switch verb {
	case "go:build":
		if c.Pos() > s.f.Package {
			return unsup("file selection in %s: %s carries the compiler directive `%s` after the package clause — gc rejects it («misplaced compiler directive»: a build constraint is consumed by the package clause only); refused by name (fail closed)", s.dir, s.pos(c), firstLine(c.Text))
		}
	case "go:noinline":
		if !s.nextDeclIsFunc(c) {
			return unsup("file selection in %s: %s carries the compiler directive `%s` that no func or method declaration follows (it is before the package clause, inside a declaration or a body, before a var/type/const/import declaration, or at the end of the file) — gc rejects it («misplaced compiler directive»: the pragma is consumed by the next func or method declaration only); refused by name (fail closed)", s.dir, s.pos(c), firstLine(c.Text))
		}
	}
	return nil
}

// ownLine is gc's `blank` flag for the comment: only whitespace precedes
// it on its line. The file's bytes are read once per file; a file whose
// size changed since the parse refuses rather than judge stale text.
func (s *directiveScan) ownLine(c *ast.Comment) (bool, error) {
	tf := s.fset.File(c.Pos())
	if tf == nil {
		return false, unsup("file selection in %s: %s — the directive's file is not in the FileSet (fail closed)", s.dir, s.pos(c))
	}
	if s.src == nil {
		b, err := os.ReadFile(tf.Name())
		if err != nil {
			return false, unsup("file selection in %s: cannot re-read %s for the directive placement rule (%v) — fail closed", s.dir, tf.Name(), err)
		}
		if len(b) != tf.Size() {
			return false, unsup("file selection in %s: %s changed on disk between the parse (%d bytes) and the directive scan (%d bytes) — fail closed", s.dir, tf.Name(), tf.Size(), len(b))
		}
		s.src = b
	}
	off := tf.Offset(c.Pos())
	lineStart := tf.Offset(tf.LineStart(tf.Line(c.Pos())))
	return strings.TrimSpace(string(s.src[lineStart:off])) == "", nil
}

// nextDeclIsFunc: the directive is at top level, after the package clause,
// and the first declaration after it (through blank lines and comments)
// is a func or method declaration — the one consumer of a `//go:noinline`
// pragma in gc's parser (syntax/parser.go takePragma at funcDeclOrNil;
// every other consumer reports the flag as misplaced).
func (s *directiveScan) nextDeclIsFunc(c *ast.Comment) bool {
	if c.Pos() < s.f.Package {
		return false // taken by the package clause: misplaced (a13)
	}
	for _, d := range s.f.Decls {
		if d.Pos() <= c.Pos() && c.Pos() < d.End() {
			return false // inside a declaration or a body (a1, a17)
		}
		if d.Pos() > c.Pos() {
			_, ok := d.(*ast.FuncDecl)
			return ok // a2/a7/a11/a18 (a GenDecl) vs a9/a12/a16 (a FuncDecl)
		}
	}
	return false // the end of the file (a6)
}

// pos is `file:line:col`, the file relative to dir when it lies under it
// (the message already names dir), else as the FileSet has it.
func (s *directiveScan) pos(c *ast.Comment) string {
	p := s.fset.Position(c.Pos())
	name := p.Filename
	if rel, err := filepath.Rel(s.dir, name); err == nil && !strings.HasPrefix(rel, "..") {
		name = rel
	}
	return fmt.Sprintf("%s:%d:%d", name, p.Line, p.Column)
}
