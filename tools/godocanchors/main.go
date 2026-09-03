// Command godocanchors resolves `godoc:` citations against the PINNED Go
// standard-library source (stdlib source-through slice 1, 2026-09-03;
// design memo docs/2026-09-03_stdlib-boundary-design.md Appendix D, gate
// G3 ruled AS RECOMMENDED by the [USER], relayed). It is the resolver
// scripts/check-spec-anchors calls for the third citation grammar:
//
//	godoc:<import path>.<Ident>[.<Method>]@<rev>
//
// e.g. godoc:strings.Fields@go1.26.5, godoc:strconv.NumError.Error@go1.26.5.
// Resolution means: <rev> equals the pinned oracle toolchain (first line of
// baselines/go-oracle-pin), and deps/go/src/<import path> — parsed with
// go/parser over its non-test .go files, ALL build contexts (a doc anchor
// is about the declaration, not about which file gc selected) — declares a
// package-level Ident (func/type/var/const) and, when a Method is given, a
// method of that name whose receiver is Ident. Like check-spec-anchors this
// checks RESOLUTION only, never quote fidelity.
//
// Usage: godocanchors [--src deps/go/src] [--pin baselines/go-oracle-pin] < anchors
// (one `godoc:...` token per line; exit 1 listing every unresolved one;
// exit 2 on a harness failure — a resolver that cannot run FAILS, never
// skips). Stdlib only, GO111MODULE=off.
package main

import (
	"bufio"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"regexp"
	"strings"
)

var anchorRE = regexp.MustCompile(`^godoc:([A-Za-z0-9_/]+)\.([A-Za-z_][A-Za-z0-9_]*)(?:\.([A-Za-z_][A-Za-z0-9_]*))?@(go[0-9][0-9.]*(?:rc[0-9]+|beta[0-9]+)?)$`)

func main() {
	src := flag.String("src", "deps/go/src", "pinned GOROOT source root")
	pin := flag.String("pin", "baselines/go-oracle-pin", "oracle toolchain pin file")
	flag.Parse()
	pinData, err := os.ReadFile(*pin)
	if err != nil {
		fmt.Fprintf(os.Stderr, "godocanchors: cannot read %s: %v (fail closed)\n", *pin, err)
		os.Exit(2)
	}
	pinned := strings.TrimSpace(strings.SplitN(string(pinData), "\n", 2)[0])
	versionFile := filepath.Join(*src, "..", "VERSION")
	vdata, err := os.ReadFile(versionFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "godocanchors: cannot read %s: %v — run scripts/setup-deps --only go (fail closed)\n", versionFile, err)
		os.Exit(2)
	}
	if have := strings.TrimSpace(strings.SplitN(string(vdata), "\n", 2)[0]); have != pinned {
		fmt.Fprintf(os.Stderr, "godocanchors: %s is at %q, oracle pin is %q (rev drift; fail closed)\n", versionFile, have, pinned)
		os.Exit(2)
	}

	type pkgDecls struct {
		idents  map[string]bool
		methods map[string]map[string]bool // type -> method set
	}
	cache := map[string]*pkgDecls{}
	load := func(path string) (*pkgDecls, error) {
		if d, ok := cache[path]; ok {
			return d, nil
		}
		dir := filepath.Join(*src, filepath.FromSlash(path))
		entries, err := os.ReadDir(dir)
		if err != nil {
			return nil, fmt.Errorf("no package directory %s", dir)
		}
		d := &pkgDecls{idents: map[string]bool{}, methods: map[string]map[string]bool{}}
		fset := token.NewFileSet()
		files := 0
		for _, ent := range entries {
			name := ent.Name()
			if ent.IsDir() || filepath.Ext(name) != ".go" || strings.HasSuffix(name, "_test.go") {
				continue
			}
			f, err := parser.ParseFile(fset, filepath.Join(dir, name), nil, parser.SkipObjectResolution)
			if err != nil {
				return nil, fmt.Errorf("parse %s: %v", name, err)
			}
			files++
			for _, decl := range f.Decls {
				switch x := decl.(type) {
				case *ast.FuncDecl:
					if x.Recv == nil {
						d.idents[x.Name.Name] = true
						continue
					}
					if len(x.Recv.List) == 1 {
						rt := x.Recv.List[0].Type
						if star, ok := rt.(*ast.StarExpr); ok {
							rt = star.X
						}
						if ix, ok := rt.(*ast.IndexExpr); ok { // generic receiver T[P]
							rt = ix.X
						}
						if il, ok := rt.(*ast.IndexListExpr); ok {
							rt = il.X
						}
						if id, ok := rt.(*ast.Ident); ok {
							if d.methods[id.Name] == nil {
								d.methods[id.Name] = map[string]bool{}
							}
							d.methods[id.Name][x.Name.Name] = true
						}
					}
				case *ast.GenDecl:
					for _, spec := range x.Specs {
						switch s := spec.(type) {
						case *ast.TypeSpec:
							d.idents[s.Name.Name] = true
						case *ast.ValueSpec:
							for _, n := range s.Names {
								d.idents[n.Name] = true
							}
						}
					}
				}
			}
		}
		if files == 0 {
			return nil, fmt.Errorf("no non-test .go files in %s", dir)
		}
		cache[path] = d
		return d, nil
	}

	sc := bufio.NewScanner(os.Stdin)
	n, bad := 0, 0
	for sc.Scan() {
		tok := strings.TrimSpace(sc.Text())
		if tok == "" {
			continue
		}
		n++
		m := anchorRE.FindStringSubmatch(tok)
		if m == nil {
			fmt.Printf("  UNPARSED %s (grammar: godoc:<import path>.<Ident>[.<Method>]@<rev>)\n", tok)
			bad++
			continue
		}
		path, ident, method, rev := m[1], m[2], m[3], m[4]
		if rev != pinned {
			fmt.Printf("  UNRESOLVED %s — rev %s is not the oracle pin %s\n", tok, rev, pinned)
			bad++
			continue
		}
		d, err := load(path)
		if err != nil {
			fmt.Printf("  UNRESOLVED %s — %v\n", tok, err)
			bad++
			continue
		}
		if !d.idents[ident] {
			fmt.Printf("  UNRESOLVED %s — no package-level declaration %s in %s at %s\n", tok, ident, path, pinned)
			bad++
			continue
		}
		if method != "" && !d.methods[ident][method] {
			fmt.Printf("  UNRESOLVED %s — %s has no method %s in %s at %s\n", tok, ident, method, path, pinned)
			bad++
			continue
		}
	}
	if err := sc.Err(); err != nil {
		fmt.Fprintf(os.Stderr, "godocanchors: reading anchors: %v (fail closed)\n", err)
		os.Exit(2)
	}
	fmt.Printf("godocanchors: %d godoc: citations, %d unresolved (pin %s)\n", n, bad, pinned)
	if bad > 0 {
		os.Exit(1)
	}
}
