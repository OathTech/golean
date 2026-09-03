// Command cedarcensus is LANE TOOLING for the cedar-go coverage census
// (docs/2026-09-03_cedar-go-coverage-census.md; runner scripts/cedar-census).
// Not a gate, not part of the trusted surface; stdlib only, GO111MODULE=off.
//
//	cedarcensus inventory <root> <modpath>   per-package TSV: dir, name, files, loc, funcs, methods,
//	                                          stdlib imports, module-internal imports, external imports
//	cedarcensus decls <file-or-dir>...        per-declaration TSV: file, line, kind, name, loc
//	cedarcensus wire <wire.json>              per-declaration TSV from a golean-native-v1 wire:
//	                                          pkg, kind, name, status (lowered|quarantined), cause, class, key
//	cedarcensus classify                      stdin cause lines -> class TAB key (same taxonomy)
//	cedarcensus demand <srcroot> <pkgpath>...  STATIC per-function demand census over the assembled
//	                                          source copy: which unmodeled stdlib selectors / refused
//	                                          language shapes each function body demands, judged
//	                                          against the supply table of docs/2026-09-03_stdlib-
//	                                          boundary-design.md §1.2 (frozen shims + shadow types +
//	                                          machine-owned sync/slices.Sort). Used because the
//	                                          frontend's whole-export kill points (H-11 initializers,
//	                                          unstubbable iter.Seq2 signatures) hide the per-function
//	                                          picture behind one refusal.
//
// The `wire` classification reuses the $GOROOT/test triage's cause taxonomy
// (docs/2026-09-01_gotest-triage.md) keyed to the FR-n rows of
// docs/language-coverage-ledger.md; an unmatched cause lands in `other`
// with its text intact — never absorbed.
package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
)

func main() {
	if len(os.Args) < 2 || (len(os.Args) < 3 && os.Args[1] != "classify") {
		fmt.Fprintln(os.Stderr, "usage: cedarcensus inventory <root> <modpath> | decls <path>... | wire <wire.json> | demand <srcroot> <pkgpath>... | classify")
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
	case "wire":
		err = wire(os.Args[2])
	case "classify":
		err = classifyStdin()
	case "demand":
		if len(os.Args) < 4 {
			err = fmt.Errorf("demand needs <srcroot> <pkgpath>...")
		} else {
			err = demand(os.Args[2], os.Args[3:])
		}
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

// ---- wire classification -------------------------------------------------

type rule struct {
	re    *regexp.Regexp
	class string
	key   func(m []string) string
}

var methodWrap = regexp.MustCompile(`^method \S+ \((.*)\)$`)

var rules = []rule{
	{regexp.MustCompile(`golean (\S+) shim RUNTIME refusal`), "stdlib-call", func(m []string) string { return m[1] + " (shim bound)" }},
	{regexp.MustCompile(`golean stdlib shim RUNTIME refusal`), "shim-injected", func(m []string) string { return "shim runtime-refusal helper (injected, not a library decl)" }},
	{regexp.MustCompile(`(\w+)\.(\w+) is outside the modeled subset`), "stdlib-call", func(m []string) string { return m[1] + "." + m[2] }},
	{regexp.MustCompile(`fmt\.(\w+) verb (%\w) over an argument of type (\S+)`), "stdlib-call", func(m []string) string { return "fmt." + m[1] + " verb " + m[2] + " @" + m[3] }},
	{regexp.MustCompile(`imported method ([\w/]+\.\w+\.\w+) \(declaration-only stub`), "stdlib-type-method", func(m []string) string { return m[1] }},
	{regexp.MustCompile(`instantiation of imported generic type ([\w/]+\.\w+)`), "stdlib-generic", func(m []string) string { return m[1] + " (imported generic instantiation; iterator API)" }},
	{regexp.MustCompile(`package-selector call ([\w/]+)\.(\w+) \(package`), "stdlib-call", func(m []string) string { return m[1] + "." + m[2] }},
	{regexp.MustCompile(`selector call (\w+) is not a method value`), "stdlib-call", func(m []string) string { return "?." + m[1] + " (FR-14 misattributing string)" }},
	{regexp.MustCompile(`sync\.(\w+)\.(\w+)`), "sync-surface", func(m []string) string { return "sync." + m[1] + "." + m[2] }},
	{regexp.MustCompile(`slices\.Sort at non-integer element type (\S+)`), "stdlib-call", func(m []string) string { return "slices.Sort@" + m[1] + " (FR-14)" }},
	{regexp.MustCompile(`imported generic instantiation ([\w/]+\.\w+)`), "stdlib-generic", func(m []string) string { return m[1] }},
	{regexp.MustCompile(`imported named type ([\w/]+\.\w+)`), "stdlib-type", func(m []string) string { return m[1] }},
	{regexp.MustCompile(`imported (?:named )?type ([\w/]+\.\w+)`), "stdlib-type", func(m []string) string { return m[1] }},
	{regexp.MustCompile(`unsafe\.`), "unsafe", func(m []string) string { return "unsafe.*" }},
	{regexp.MustCompile(`reflect\.`), "reflect", func(m []string) string { return "reflect.*" }},
	{regexp.MustCompile(`builtin (print|println)`), "builtin-print", func(m []string) string { return m[1] }},
	{regexp.MustCompile(`range over .*func`), "lang FR-12 range-over-func", func(m []string) string { return "range-over-func" }},
	{regexp.MustCompile(`range over (\S+)`), "lang FR-12 range-over-func", func(m []string) string { return "range over " + m[1] }},
	{regexp.MustCompile(`anonymous non-empty struct`), "lang FR-13 anon-struct", func(m []string) string { return "anonymous struct" }},
	{regexp.MustCompile(`go of builtin`), "lang FR-1", func(m []string) string { return "go of builtin" }},
	{regexp.MustCompile(`channel receive in`), "lang FR-2", func(m []string) string { return "recv in short-circuit" }},
	{regexp.MustCompile(`method expression \(\*`), "lang FR-3", func(m []string) string { return "(*T).Mv adapter" }},
	{regexp.MustCompile(`range assignment to non-identifier`), "lang FR-6", func(m []string) string { return "range assign non-ident" }},
	{regexp.MustCompile(`implicit interface conversion in multi-value`), "lang FR-7 tuple-iface-box", func(m []string) string { return "tuple component boxing" }},
	{regexp.MustCompile(`goto`), "lang FR-11/20 goto", func(m []string) string { return "goto" }},
	{regexp.MustCompile(`complex`), "lang FR-15 complex", func(m []string) string { return "complex" }},
	{regexp.MustCompile(`defer of builtin`), "lang FR-16", func(m []string) string { return "defer of builtin" }},
	{regexp.MustCompile(`self-shadowing define`), "lang FR-17", func(m []string) string { return "self-shadow define" }},
	{regexp.MustCompile(`in short-circuit operand`), "lang FR-18", func(m []string) string { return "alloc/call in short-circuit" }},
	{regexp.MustCompile(`duplicate TypeId`), "lang FR-19", func(m []string) string { return "duplicate TypeId" }},
	{regexp.MustCompile(`generic|type parameter|instantiat|stencil`), "generics-corner", func(m []string) string { return firstWords(m[0], 6) }},
}

func firstWords(s string, n int) string {
	w := strings.Fields(s)
	if len(w) > n {
		w = w[:n]
	}
	return strings.Join(w, " ")
}

func classify(cause string) (class, key string) {
	inner := cause
	if m := methodWrap.FindStringSubmatch(cause); m != nil {
		inner = m[1]
	}
	for _, r := range rules {
		if m := r.re.FindStringSubmatch(inner); m != nil {
			return r.class, r.key(m)
		}
	}
	// Unmatched: keep the head of the text as the key so it aggregates
	// without being absorbed into a known class.
	head := inner
	if i := strings.IndexAny(head, ":("); i > 0 {
		head = head[:i]
	}
	return "other", strings.TrimSpace(firstWords(head, 8))
}

func pkgOf(name string) string {
	// FuncId / TypeId grammar: `<pkgpath>.<Name>[.<Method>]`, main package
	// declarations unqualified.
	i := strings.Index(name, ".")
	if i < 0 {
		return "main"
	}
	if strings.Contains(name[:i], "/") || isLower(name[:i]) {
		return name[:i]
	}
	return "main"
}

func isLower(s string) bool {
	return s != "" && s[0] >= 'a' && s[0] <= 'z'
}

func wire(path string) error {
	b, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	var prog map[string]any
	if err := json.Unmarshal(b, &prog); err != nil {
		return err
	}
	fmt.Println("pkg\tkind\tname\tstatus\tcause\tclass\tkey")
	row := func(kind, name string, unsupported any) {
		status, cause, class, key := "lowered", "-", "-", "-"
		if s, ok := unsupported.(string); ok {
			status, cause = "quarantined", strings.ReplaceAll(s, "\t", " ")
			class, key = classify(s)
		}
		fmt.Printf("%s\t%s\t%s\t%s\t%s\t%s\t%s\n", pkgOf(name), kind, name, status, cause, class, key)
	}
	for _, f := range asList(prog["funcs"]) {
		row("func", str(f["name"]), f["unsupported"])
	}
	for _, m := range asList(prog["methods"]) {
		if w, _ := m["wrapper"].(bool); w {
			continue // synthesized promotion wrappers are not source declarations
		}
		if _, isIface := m["interface"]; isIface {
			continue // interface method anchors
		}
		row("method", str(m["recvType"])+"."+str(m["name"]), m["unsupported"])
	}
	for _, t := range asList(prog["types"]) {
		def, _ := t["def"].(map[string]any)
		var u any
		if def != nil && str(def["kind"]) == "unsupported" {
			u = str(def["feature"])
		}
		row("type", str(t["name"]), u)
	}
	return nil
}

func classifyStdin() error {
	sc := bufio.NewScanner(os.Stdin)
	sc.Buffer(make([]byte, 1<<20), 1<<20)
	for sc.Scan() {
		c, k := classify(sc.Text())
		fmt.Printf("%s\t%s\n", c, k)
	}
	return sc.Err()
}

func asList(v any) []map[string]any {
	xs, _ := v.([]any)
	out := make([]map[string]any, 0, len(xs))
	for _, x := range xs {
		if m, ok := x.(map[string]any); ok {
			out = append(out, m)
		}
	}
	return out
}

func str(v any) string {
	s, _ := v.(string)
	return s
}
