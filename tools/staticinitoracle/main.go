// staticinitoracle — gc's verdict, shape by shape, for the BUG-061
// classifier's table (tools/nativefrontend/testdata/staticinit-shapes.go).
//
// For every `var` spec of the shapes file it builds a package holding the
// file's preamble (imports, types, functions), the `// base` specs and
// that one spec, with the pinned toolchain in GOPATH mode, and reads the
// package's `..inittask` record out of the archive with `go tool nm
// -size`: no record, or a record of the 8-byte header alone (nfns = 0 —
// the record exists only because an import bears one), means gc folded
// every initializer (verdict `none`); a longer record carries the
// package's own init function (verdict `work`). The bases alone must be
// `none`, else the oracle refuses to record. The record is read from the
// COMPILE ARCHIVE: the linker drops a deps-only record from a linked
// binary, so `go tool nm` on a binary cannot tell «no record» from
// «record with no function» (the reviewer's d01_depsonly probe); the
// archive keeps every record the compiler emitted. Output: a TSV `key<TAB>verdict`
// with a header naming the toolchain, read by staticinit_test.go and
// diffed by scripts/test-staticinit-oracle (a self-test, not a gate).
//
// Keys: the spec's names joined by ","; a blank spec is `_<n>` by order of
// appearance. Written for the fix round of 2026-10-12 ([AGENT]; the
// review's HIGH: the classifier's expectations must be gc's, recorded).
package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
)

type shape struct {
	key  string
	text string // the spec's source text
	base bool
}

func main() {
	shapesPath := flag.String("shapes", "", "the shapes file (package shapes, one var spec per shape)")
	otherPath := flag.String("other", "", "the `other` package source the shapes import")
	out := flag.String("out", "", "output TSV path (default stdout)")
	flag.Parse()
	if *shapesPath == "" || *otherPath == "" {
		fmt.Fprintln(os.Stderr, "staticinitoracle: --shapes and --other are required")
		os.Exit(2)
	}
	tsv, err := record(*shapesPath, *otherPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "staticinitoracle: %v\n", err)
		os.Exit(2)
	}
	if *out == "" {
		os.Stdout.WriteString(tsv)
		return
	}
	if err := os.WriteFile(*out, []byte(tsv), 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "staticinitoracle: %v\n", err)
		os.Exit(2)
	}
}

func record(shapesPath, otherPath string) (string, error) {
	src, err := os.ReadFile(shapesPath)
	if err != nil {
		return "", err
	}
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, shapesPath, src, parser.ParseComments)
	if err != nil {
		return "", err
	}
	// The preamble: every top-level declaration that is not the var
	// block(s), as written. Imports are re-derived per package.
	var preamble []string
	var shapes []shape
	blanks := 0
	for _, d := range f.Decls {
		gd, isGen := d.(*ast.GenDecl)
		if isGen && gd.Tok == token.IMPORT {
			continue
		}
		if !isGen || gd.Tok != token.VAR {
			// With its doc comment: a `//go:noinline` pragma is part of
			// the shape.
			start := d.Pos()
			if fd, ok := d.(*ast.FuncDecl); ok && fd.Doc != nil {
				start = fd.Doc.Pos()
			} else if isGen && gd.Doc != nil {
				start = gd.Doc.Pos()
			}
			preamble = append(preamble, string(src[fset.Position(start).Offset:fset.Position(d.End()).Offset]))
			continue
		}
		for _, spec := range gd.Specs {
			vs := spec.(*ast.ValueSpec)
			names := []string{}
			for _, n := range vs.Names {
				if n.Name == "_" {
					blanks++
					names = append(names, "_"+strconv.Itoa(blanks))
				} else {
					names = append(names, n.Name)
				}
			}
			sh := shape{
				key:  strings.Join(names, ","),
				text: string(src[fset.Position(vs.Pos()).Offset:fset.Position(vs.End()).Offset]),
			}
			if vs.Comment != nil && strings.Contains(vs.Comment.Text(), "base") {
				sh.base = true
			}
			shapes = append(shapes, sh)
		}
	}
	if len(shapes) == 0 {
		return "", fmt.Errorf("%s: no var specs", shapesPath)
	}
	other, err := os.ReadFile(otherPath)
	if err != nil {
		return "", err
	}

	tmp, err := os.MkdirTemp("", "staticinit-oracle-")
	if err != nil {
		return "", err
	}
	defer os.RemoveAll(tmp)
	if err := writeFile(filepath.Join(tmp, "src", "other", "other.go"), other); err != nil {
		return "", err
	}

	var bases []shape
	for _, sh := range shapes {
		if sh.base {
			bases = append(bases, sh)
		}
	}
	// The bases alone must have no work: every verdict below is "bases +
	// one shape", so a working base would hide behind every shape.
	v, err := verdict(tmp, "bases", preamble, bases, nil)
	if err != nil {
		return "", err
	}
	if v != "none" {
		return "", fmt.Errorf("the base specs alone have initialization work (%s): the table's bases must be static", v)
	}

	goVersion, err := exec.Command("go", "version").Output()
	if err != nil {
		return "", err
	}
	var b strings.Builder
	fmt.Fprintf(&b, "# staticinit-oracle.tsv — gc's verdict per shape of staticinit-shapes.go: `none` = every initializer folded\n")
	fmt.Fprintf(&b, "# (no ..inittask record, or the 8-byte header alone), `work` = the record carries the package's init function.\n")
	fmt.Fprintf(&b, "# Recorded by scripts/test-staticinit-oracle (tools/staticinitoracle, bases + one spec per package, GOPATH mode)\n")
	fmt.Fprintf(&b, "# with %s. Re-record with `scripts/test-staticinit-oracle --record` when the shapes change.\n", strings.TrimSpace(string(goVersion)))
	fmt.Fprintf(&b, "key\tverdict\n")
	for i, sh := range shapes {
		var extra []shape
		if !sh.base {
			extra = []shape{sh}
		}
		v, err := verdict(tmp, fmt.Sprintf("s%03d", i), preamble, bases, extra)
		if err != nil {
			return "", fmt.Errorf("shape %s: %v", sh.key, err)
		}
		fmt.Fprintf(&b, "%s\t%s\n", sh.key, v)
	}
	return b.String(), nil
}

var inittaskLine = regexp.MustCompile(`^\s*[0-9a-fA-F]*\s+(\d+)\s+D\s+(\S+)\.\.inittask$`)

// verdict builds bases + extra as the package importPath and reads its
// inittask record.
func verdict(tmp, importPath string, preamble []string, bases, extra []shape) (string, error) {
	var b strings.Builder
	b.WriteString("package shapes\n\n")
	body := strings.Join(preamble, "\n\n") + "\n"
	var specs []string
	for _, sh := range append(append([]shape{}, bases...), extra...) {
		specs = append(specs, sh.text)
	}
	varBlock := "var (\n\t" + strings.Join(specs, "\n\t") + "\n)\n"
	for _, imp := range []string{"errors", "other", "unsafe"} {
		if strings.Contains(varBlock, imp+".") {
			fmt.Fprintf(&b, "import %q\n", imp)
		}
	}
	b.WriteString("\n" + body + "\n" + varBlock)
	dir := filepath.Join(tmp, "src", importPath)
	if err := writeFile(filepath.Join(dir, "shapes.go"), []byte(b.String())); err != nil {
		return "", err
	}
	archive := filepath.Join(tmp, importPath+".a")
	build := exec.Command("go", "build", "-o", archive, importPath)
	build.Env = append(os.Environ(), "GO111MODULE=off", "GOPATH="+tmp, "GOFLAGS=")
	if outb, err := build.CombinedOutput(); err != nil {
		return "", fmt.Errorf("go build failed (fail closed):\n%s\n--- source:\n%s", outb, b.String())
	}
	nm := exec.Command("go", "tool", "nm", "-size", archive)
	outb, err := nm.Output()
	if err != nil {
		return "", fmt.Errorf("go tool nm: %v", err)
	}
	for _, line := range strings.Split(string(outb), "\n") {
		m := inittaskLine.FindStringSubmatch(line)
		if m == nil || m[2] != importPath {
			continue
		}
		size, err := strconv.Atoi(m[1])
		if err != nil {
			return "", fmt.Errorf("nm size %q: %v", m[1], err)
		}
		if size > 8 {
			return "work", nil
		}
		return "none", nil
	}
	if bytes.Contains(outb, []byte(importPath+"..inittask")) {
		return "", fmt.Errorf("an inittask line for %s did not parse:\n%s", importPath, outb)
	}
	return "none", nil
}

func writeFile(path string, data []byte) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	return os.WriteFile(path, data, 0o644)
}
