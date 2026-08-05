// Command nativefrontend is the native Go frontend for GoLean: it parses and
// type-checks a Go package with the standard library (go/parser + go/types)
// and emits the native wire schema (golean-native-v1) that
// GoLean/NativeJson.lean decodes and GoLean/NativeToIR.lean lowers into GoCore.
// Stdlib only; no external dependencies. Runs under GO111MODULE=off.
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"sort"
)

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, "nativefrontend:", err)
		os.Exit(1)
	}
}

func run() error {
	// Materialized type aliases (generics G4, design-note decision §9.5):
	// a GOPATH-mode binary inherits the toolchain's COMPATIBILITY default
	// gotypesalias=0, under which go/types ABORTS on generic type alias
	// declarations ("requires GODEBUG=gotypesalias=1 or unset"). The
	// GODEBUG environment variable overrides that default and is watched
	// at runtime, so setting it here — before any go/types use — enables
	// materialized *types.Alias everywhere (probe-verified 2026-08-05).
	// Existing settings are preserved; the LAST occurrence of a key wins.
	if g := os.Getenv("GODEBUG"); g != "" {
		os.Setenv("GODEBUG", g+",gotypesalias=1")
	} else {
		os.Setenv("GODEBUG", "gotypesalias=1")
	}

	dir := flag.String("dir", "", "package directory to type-check and emit")
	out := flag.String("out", "", "output wire JSON path (default stdout)")
	flag.Parse()
	if *dir == "" {
		return fmt.Errorf("--dir is required")
	}

	fset := token.NewFileSet()
	pkgs, err := parser.ParseDir(fset, *dir, nonTestGoFile, parser.ParseComments)
	if err != nil {
		return err
	}
	if len(pkgs) != 1 {
		return fmt.Errorf("expected exactly one package in %s, found %d", *dir, len(pkgs))
	}

	var files []*ast.File
	for _, pkg := range pkgs {
		paths := make([]string, 0, len(pkg.Files))
		for p := range pkg.Files {
			paths = append(paths, p)
		}
		sort.Strings(paths)
		for _, p := range paths {
			files = append(files, pkg.Files[p])
		}
	}

	info := &types.Info{
		Types:      map[ast.Expr]types.TypeAndValue{},
		Defs:       map[*ast.Ident]types.Object{},
		Uses:       map[*ast.Ident]types.Object{},
		Selections: map[*ast.SelectorExpr]*types.Selection{},
		// Implicits carries the per-clause type-switch variable
		// (`switch v := x.(type)`) — each CaseClause maps to its own
		// implicitly declared *types.Var (design note 2026-08-05 D3).
		Implicits: map[ast.Node]types.Object{},
		// Instances maps each identifier denoting a generic function/type
		// at a USE site to its (fully inferred) type arguments and
		// instantiated type — the input to frontend monomorphization
		// (generics design note 2026-08-05 §2a). Inside generic bodies the
		// recorded arguments still mention the ENCLOSING type parameters;
		// the substitution closure resolves those per stencil (mono.go).
		Instances: map[*ast.Ident]types.Instance{},
	}
	conf := types.Config{Importer: importer.Default()}
	tpkg, err := conf.Check(files[0].Name.Name, fset, files, info)
	if err != nil {
		return fmt.Errorf("type-check: %w", err)
	}

	em := &emitter{fset: fset, info: info, pkg: tpkg}
	program, err := em.emitProgram(files)
	if err != nil {
		return err
	}

	encoded, err := json.MarshalIndent(program, "", " ")
	if err != nil {
		return err
	}
	if *out == "" || *out == "-" {
		_, err = os.Stdout.Write(append(encoded, '\n'))
		return err
	}
	return os.WriteFile(*out, encoded, 0o644)
}

func nonTestGoFile(fi os.FileInfo) bool {
	name := fi.Name()
	return filepath.Ext(name) == ".go" && !hasSuffix(name, "_test.go")
}

func hasSuffix(s, suf string) bool {
	return len(s) >= len(suf) && s[len(s)-len(suf):] == suf
}
