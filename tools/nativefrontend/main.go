// Command nativefrontend is the native Go frontend for GoLean: it parses and
// type-checks a Go package with the standard library (go/parser + go/types)
// and lowers it to the GoCore wire schema. This first cut proves the go/types
// foundation on real corpus input by resolving and printing the package's
// types, functions, and methods; wire emission is layered on next.
package main

import (
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
	dir := flag.String("dir", "", "package directory to type-check")
	flag.Parse()
	if *dir == "" {
		return fmt.Errorf("--dir is required")
	}

	fset := token.NewFileSet()
	pkgs, err := parser.ParseDir(fset, *dir, nonTestGoFile, 0)
	if err != nil {
		return err
	}

	for name, pkg := range pkgs {
		files := make([]*ast.File, 0, len(pkg.Files))
		paths := make([]string, 0, len(pkg.Files))
		for p := range pkg.Files {
			paths = append(paths, p)
		}
		sort.Strings(paths)
		for _, p := range paths {
			files = append(files, pkg.Files[p])
		}

		info := &types.Info{
			Types:      map[ast.Expr]types.TypeAndValue{},
			Defs:       map[*ast.Ident]types.Object{},
			Uses:       map[*ast.Ident]types.Object{},
			Selections: map[*ast.SelectorExpr]*types.Selection{},
		}
		conf := types.Config{Importer: importer.Default()}
		tpkg, err := conf.Check(name, fset, files, info)
		if err != nil {
			return fmt.Errorf("type-check %s: %w", name, err)
		}

		fmt.Printf("package %s\n", tpkg.Name())
		scope := tpkg.Scope()
		for _, n := range scope.Names() {
			obj := scope.Lookup(n)
			switch o := obj.(type) {
			case *types.TypeName:
				named, _ := o.Type().(*types.Named)
				underlying := o.Type().Underlying()
				fmt.Printf("  type %s = underlying %s\n", o.Name(), underlying)
				if named != nil {
					for i := 0; i < named.NumMethods(); i++ {
						m := named.Method(i)
						fmt.Printf("    method %s%s\n", m.Name(), m.Type().(*types.Signature).String()[len("func"):])
					}
				}
			case *types.Func:
				fmt.Printf("  func %s%s\n", o.Name(), o.Type().(*types.Signature).String()[len("func"):])
			}
		}
	}
	return nil
}

func nonTestGoFile(fi os.FileInfo) bool {
	name := fi.Name()
	return filepath.Ext(name) == ".go" && !hasSuffix(name, "_test.go")
}

func hasSuffix(s, suf string) bool {
	return len(s) >= len(suf) && s[len(s)-len(suf):] == suf
}
