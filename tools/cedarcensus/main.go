// Command cedarcensus is LANE TOOLING for the cedar-go coverage census
// (docs/2026-09-03_cedar-go-coverage-census.md; runner scripts/cedar-census).
// Not a gate, not part of the trusted surface; stdlib only, GO111MODULE=off.
//
//	cedarcensus inventory <root> <modpath>   per-package TSV: dir, name, files, loc, funcs, methods,
//	                                          stdlib imports, module-internal imports, external imports
//	cedarcensus decls <file-or-dir>...        per-declaration TSV: file, line, kind, name, loc
//
// The per-declaration WIRE classification (`wire`), `classify` and the STATIC
// `demand` census moved to tools/lowerdiag 2026-09-04 ([USER] direction 4 —
// one implementation of the cause taxonomy, tools/lowerdiag/causes.tsv,
// checked against the ledger's FR ids); scripts/cedar-census calls lowerdiag.
package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
)

func main() {
	if len(os.Args) < 3 {
		fmt.Fprintln(os.Stderr, "usage: cedarcensus inventory <root> <modpath> | decls <path>... (wire/classify/demand: tools/lowerdiag)")
		os.Exit(2)
	}
	var err error
	switch os.Args[1] {
	case "inventory":
		if len(os.Args) != 4 {
			err = fmt.Errorf("inventory needs <root> <modpath>")
		} else {
			err = inventory(os.Args[2], os.Args[3])
		}
	case "decls":
		err = decls(os.Args[2:])
	default:
		err = fmt.Errorf("unknown subcommand %q", os.Args[1])
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "cedarcensus:", err)
		os.Exit(1)
	}
}

func nonTest(fi os.FileInfo) bool {
	n := fi.Name()
	return strings.HasSuffix(n, ".go") && !strings.HasSuffix(n, "_test.go")
}

func countLines(path string) (int, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return 0, err
	}
	return strings.Count(string(b), "\n"), nil
}

func inventory(root, modpath string) error {
	root = filepath.Clean(root)
	var dirs []string
	err := filepath.Walk(root, func(p string, fi os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if fi.IsDir() {
			if fi.Name() == "testdata" || strings.HasPrefix(fi.Name(), ".") && p != root {
				return filepath.SkipDir
			}
			dirs = append(dirs, p)
		}
		return nil
	})
	if err != nil {
		return err
	}
	sort.Strings(dirs)
	fmt.Println("dir\tpackage\tfiles\tloc\tfuncs\tmethods\tstdlib_imports\tinternal_imports\texternal_imports")
	for _, d := range dirs {
		fset := token.NewFileSet()
		pkgs, err := parser.ParseDir(fset, d, nonTest, parser.ImportsOnly|parser.ParseComments)
		if err != nil {
			return fmt.Errorf("%s: %v", d, err)
		}
		if len(pkgs) == 0 {
			continue
		}
		if len(pkgs) != 1 {
			return fmt.Errorf("%s: %d packages in one dir", d, len(pkgs))
		}
		var pkg *ast.Package
		for _, p := range pkgs {
			pkg = p
		}
		// Full parse for decl counts.
		full, err := parser.ParseDir(fset, d, nonTest, 0)
		if err != nil {
			return err
		}
		funcs, methods, loc := 0, 0, 0
		for _, p := range full {
			for path, f := range p.Files {
				n, err := countLines(path)
				if err != nil {
					return err
				}
				loc += n
				for _, decl := range f.Decls {
					if fd, ok := decl.(*ast.FuncDecl); ok {
						if fd.Recv != nil {
							methods++
						} else {
							funcs++
						}
					}
				}
			}
		}
		std, internal, external := map[string]bool{}, map[string]bool{}, map[string]bool{}
		for _, f := range pkg.Files {
			for _, im := range f.Imports {
				p, _ := strconv.Unquote(im.Path.Value)
				switch {
				case p == modpath || strings.HasPrefix(p, modpath+"/"):
					internal[strings.TrimPrefix(strings.TrimPrefix(p, modpath), "/")] = true
				case strings.Contains(strings.SplitN(p, "/", 2)[0], "."):
					external[p] = true
				default:
					std[p] = true
				}
			}
		}
		rel, _ := filepath.Rel(root, d)
		if rel == "" {
			rel = "."
		}
		fmt.Printf("%s\t%s\t%d\t%d\t%d\t%d\t%s\t%s\t%s\n", rel, pkg.Name, len(pkg.Files), loc, funcs, methods,
			joinKeys(std), joinKeys(internal), joinKeys(external))
	}
	return nil
}

func joinKeys(m map[string]bool) string {
	ks := make([]string, 0, len(m))
	for k := range m {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	if len(ks) == 0 {
		return "-"
	}
	return strings.Join(ks, ",")
}

func decls(paths []string) error {
	fmt.Println("file\tline\tkind\tname\tloc")
	for _, p := range paths {
		fi, err := os.Stat(p)
		if err != nil {
			return err
		}
		var files []string
		if fi.IsDir() {
			ents, err := filepath.Glob(filepath.Join(p, "*.go"))
			if err != nil {
				return err
			}
			for _, e := range ents {
				if !strings.HasSuffix(e, "_test.go") {
					files = append(files, e)
				}
			}
		} else {
			files = []string{p}
		}
		sort.Strings(files)
		for _, f := range files {
			fset := token.NewFileSet()
			af, err := parser.ParseFile(fset, f, nil, 0)
			if err != nil {
				return err
			}
			for _, d := range af.Decls {
				fd, ok := d.(*ast.FuncDecl)
				if !ok {
					continue
				}
				kind, name := "func", fd.Name.Name
				if fd.Recv != nil {
					kind = "method"
					name = recvName(fd.Recv.List[0].Type) + "." + name
				}
				start := fset.Position(fd.Pos()).Line
				end := fset.Position(fd.End()).Line
				fmt.Printf("%s\t%d\t%s\t%s\t%d\n", f, start, kind, name, end-start+1)
			}
		}
	}
	return nil
}

func recvName(e ast.Expr) string {
	switch t := e.(type) {
	case *ast.StarExpr:
		return recvName(t.X)
	case *ast.Ident:
		return t.Name
	case *ast.IndexExpr:
		return recvName(t.X)
	case *ast.IndexListExpr:
		return recvName(t.X)
	}
	return fmt.Sprintf("%T", e)
}
