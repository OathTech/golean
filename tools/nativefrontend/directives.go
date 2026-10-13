package main

// directives.go — COMPILER DIRECTIVES in user units (release-readiness
// rows 38 and 39; the Codex zero-context pass F2/F3,
// docs/2026-10-13_codex-zero-context-pass.md; BUG-127, BUG-128; RULED
// [USER] Mike 2026-10-13, verbatim, relayed by the [AGENT] coordinator:
// «3, agree» — refuse by name, at file selection, every user unit; and
// the standing preference, Mike 2026-10-13 on BUG-125: «I feel like this
// is just opening the door to endless special-case nonsense. I'd prefer
// to just refuse this case, and maybe support it later»; lane
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
// ships with a clean export. No directive is modeled here; the ones with
// no effect on the compiled program are allowed by name, every other one
// REFUSES the export at file selection, in the root package and in every
// case-local imported package alike (both go through selectPackageFiles).
//
// gc's recognition rule (cmd/compile/internal/syntax/parser.go, the
// pragma handler): a comment whose text (after `//` or `/*`) begins
// `go:` is a directive in ANY column — the verb runs to the first blank;
// a verb gc does not know is IGNORED outside the standard library
// (noder.go: the «not allowed» error is std-only), so refusing an
// unknown verb is over-refusal in the fail-closed direction, as ruled.
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
	"path/filepath"
	"strings"
)

// allowedDirectiveVerbs is THE ALLOWLIST ([AGENT] proposal ratified by
// the [USER]'s «3, agree»): verb -> why it has no effect on the modeled
// program. Widening it is a ruling, not an edit.
var allowedDirectiveVerbs = map[string]string{
	"go:build":    "a build constraint — judged by the langversion.go policy (reserved tags refuse, a custom tag must be inert)",
	"go:noinline": "an inlining hint: optimisation only, no semantic effect (ten corpus files carry it)",
	"go:generate": "a command line for `go generate`, never read by the compiler",
}

// allowedDirectiveList is the allowlist as the refusal text states it.
const allowedDirectiveList = "//go:build, //go:noinline, //go:generate"

// refuseCompilerDirectives scans every comment of the SELECTED files for
// a directive and refuses the first one outside the allowlist, naming the
// directive, the file and the position. Called from selectPackageFiles,
// so the root package and every imported local unit are covered by the
// one site.
func refuseCompilerDirectives(fset *token.FileSet, dir string, files []*ast.File) error {
	for _, f := range files {
		for _, group := range f.Comments {
			for _, c := range group.List {
				if err := judgeDirectiveComment(fset, dir, c); err != nil {
					return err
				}
			}
		}
	}
	return nil
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

func judgeDirectiveComment(fset *token.FileSet, dir string, c *ast.Comment) error {
	body := directiveBody(c.Text)
	switch {
	case strings.HasPrefix(body, "line "):
		return unsup("file selection in %s: %s carries the line directive `%s` — position rewriting is not modeled (gc honours //line at column 1 and /*line anywhere; both forms are refused wherever they appear); RULED [USER] 2026-10-13: refuse by name (fail closed)", dir, directivePos(fset, dir, c), firstLine(c.Text))
	case strings.HasPrefix(body, "go:"):
		verb := directiveVerb(body)
		if verb == "go:debug" {
			return unsup("file selection in %s: %s carries the runtime-setting directive `%s` — GODEBUG settings are not modeled: the semantics is the Go 1.26 module defaults (panic(nil) raises *runtime.PanicNilError; the differential oracle is pinned with GODEBUG=panicnil=0); RULED [USER] 2026-10-13: refuse by name (fail closed)", dir, directivePos(fset, dir, c), firstLine(c.Text))
		}
		if _, ok := allowedDirectiveVerbs[verb]; ok {
			return nil
		}
		return unsup("file selection in %s: %s carries the compiler directive `%s` — a //go: directive outside the allowlist (%s) is not modeled (gc may embed data, rename a symbol or change code generation on it, or ignore it; none of that is modeled); RULED [USER] 2026-10-13: refuse by name, no modelling (fail closed)", dir, directivePos(fset, dir, c), firstLine(c.Text), allowedDirectiveList)
	}
	return nil
}

// directivePos is `file:line:col`, the file relative to dir when it lies
// under it (the message already names dir), else as the FileSet has it.
func directivePos(fset *token.FileSet, dir string, c *ast.Comment) string {
	p := fset.Position(c.Pos())
	name := p.Filename
	if rel, err := filepath.Rel(dir, name); err == nil && !strings.HasPrefix(rel, "..") {
		name = rel
	}
	return fmt.Sprintf("%s:%d:%d", name, p.Line, p.Column)
}
