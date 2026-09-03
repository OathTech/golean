package main

// demand.go — the STATIC per-function demand census (see main.go header).
// It type-checks the assembled dot-free source copy with go/types (the same
// checker the native frontend uses; stdlib through importer.Default, local
// packages from source) and, per function/method declaration, records
// every stdlib selector the body calls and every language shape the
// frontend is known to refuse. The verdict column judges the body against
// the SUPPLY table (what lowers today); it is a static over-approximation
// of "would the frontend quarantine this declaration" — it does not run
// the frontend, so per-declaration surprises (verb-matrix misses inside
// fmt.Sprintf, shim bounds) are outside its resolution and are said so in
// the report.

import (
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

// supplied is the supply table: selector keys that lower TODAY.
// Sources: docs/2026-09-03_stdlib-boundary-design.md §1.2 (frozen D-002
// tables, stdlibshim.go / fmtdesugar.go / genericshim.go / importedmodel.go),
// and the machine-owned surface (sync primitives, slices.Sort at ints).
var supplied = map[string]string{
	"strings.Fields": "shim", "strings.Join": "shim", "strings.Split": "shim", "strings.TrimSpace": "shim", "strings.Repeat": "shim",
	"errors.New": "shim", "bytes.Equal": "shim",
	"strconv.FormatUint": "shim", "strconv.FormatInt": "shim", "strconv.ParseUint": "shim",
	"slices.SortFunc": "shim(generic)", "cmp.Compare": "shim(generic)",
	"fmt.Sprintf": "desugar(verb matrix)", "fmt.Errorf": "desugar(verb matrix)", "fmt.Fprintf": "desugar(verb matrix)",
	"fmt.Fprint": "desugar", "fmt.Sprint": "desugar", "fmt.Sprintln": "desugar",
	"encoding/binary.LittleEndian.Uint64": "desugar", "encoding/binary.LittleEndian.PutUint64": "desugar",
	"strings.Builder.WriteString": "shadow-type", "strings.Builder.WriteByte": "shadow-type", "strings.Builder.Write": "shadow-type",
	"strings.Builder.String": "shadow-type", "strings.Builder.Len": "shadow-type", "strings.Builder.Reset": "shadow-type",
	"bytes.Buffer.WriteString": "shadow-type", "bytes.Buffer.WriteByte": "shadow-type", "bytes.Buffer.Write": "shadow-type",
	"bytes.Buffer.String": "shadow-type", "bytes.Buffer.Len": "shadow-type", "bytes.Buffer.Reset": "shadow-type",
	"slices.Sort":     "machine-op(int kinds only)",
	"sync.Mutex.Lock": "machine", "sync.Mutex.Unlock": "machine", "sync.RWMutex.Lock": "machine", "sync.RWMutex.Unlock": "machine",
	"sync.RWMutex.RLock": "machine", "sync.RWMutex.RUnlock": "machine", "sync.WaitGroup.Add": "machine", "sync.WaitGroup.Done": "machine",
	"sync.WaitGroup.Wait": "machine", "sync.Once.Do": "machine",
}

type localImporter struct {
	root  string
	fset  *token.FileSet
	cache map[string]*types.Package
	infos map[string]*types.Info
	files map[string][]*ast.File
	std   types.Importer
}

func isLocalPath(p string) bool {
	return p == "cedargo" || strings.HasPrefix(p, "cedargo/") || p == "cedark8s" || strings.HasPrefix(p, "cedark8s/") || strings.HasPrefix(p, "xexp/")
}

func (l *localImporter) Import(path string) (*types.Package, error) {
	if !isLocalPath(path) {
		return l.std.Import(path)
	}
	if p, ok := l.cache[path]; ok {
		return p, nil
	}
	dir := filepath.Join(l.root, filepath.FromSlash(path))
	pkgs, err := parser.ParseDir(l.fset, dir, nonTest, parser.ParseComments)
	if err != nil {
		return nil, err
	}
	if len(pkgs) != 1 {
		return nil, fmt.Errorf("%s: expected one package, found %d", dir, len(pkgs))
	}
	var files []*ast.File
	var names []string
	var apkg *ast.Package
	for _, p := range pkgs {
		apkg = p
		for n := range p.Files {
			names = append(names, n)
		}
	}
	sort.Strings(names)
	for _, n := range names {
		files = append(files, apkg.Files[n])
	}
	info := newInfo()
	conf := types.Config{Importer: l, Error: func(error) {}}
	pkg, err := conf.Check(path, l.fset, files, info)
	if err != nil {
		return nil, fmt.Errorf("type-check %s: %v", path, err)
	}
	l.cache[path] = pkg
	l.infos[path] = info
	l.files[path] = files
	return pkg, nil
}

func newInfo() *types.Info {
	return &types.Info{
		Types:      map[ast.Expr]types.TypeAndValue{},
		Defs:       map[*ast.Ident]types.Object{},
		Uses:       map[*ast.Ident]types.Object{},
		Selections: map[*ast.SelectorExpr]*types.Selection{},
		Implicits:  map[ast.Node]types.Object{},
		Instances:  map[*ast.Ident]types.Instance{},
	}
}

type demandSet map[string]bool

func (d demandSet) add(k string) { d[k] = true }
func (d demandSet) sorted() string {
	if len(d) == 0 {
		return "-"
	}
	ks := make([]string, 0, len(d))
	for k := range d {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	return strings.Join(ks, ",")
}

// importedNamed reports the first non-local, non-universe Named type
// reachable in t (through pointers/slices/maps/arrays/chans), else "".
// Type arguments are reported as an instantiation key.
func importedNamed(t types.Type, depth int) (key string, generic bool) {
	if depth > 6 || t == nil {
		return "", false
	}
	switch u := t.(type) {
	case *types.Named:
		obj := u.Obj()
		if obj.Pkg() == nil {
			return "", false
		}
		if !isLocalPath(obj.Pkg().Path()) {
			if u.TypeArgs() != nil && u.TypeArgs().Len() > 0 {
				return obj.Pkg().Path() + "." + obj.Name(), true
			}
			return obj.Pkg().Path() + "." + obj.Name(), false
		}
		if u.TypeArgs() != nil {
			for i := 0; i < u.TypeArgs().Len(); i++ {
				if k, g := importedNamed(u.TypeArgs().At(i), depth+1); k != "" {
					return k, g
				}
			}
		}
	case *types.Alias:
		return importedNamed(types.Unalias(u), depth+1)
	case *types.Pointer:
		return importedNamed(u.Elem(), depth+1)
	case *types.Slice:
		return importedNamed(u.Elem(), depth+1)
	case *types.Array:
		return importedNamed(u.Elem(), depth+1)
	case *types.Chan:
		return importedNamed(u.Elem(), depth+1)
	case *types.Map:
		if k, g := importedNamed(u.Key(), depth+1); k != "" {
			return k, g
		}
		return importedNamed(u.Elem(), depth+1)
	}
	return "", false
}

func anonStruct(t types.Type) bool {
	switch u := t.(type) {
	case *types.Struct:
		return u.NumFields() > 0
	case *types.Pointer:
		return anonStruct(u.Elem())
	case *types.Slice:
		return anonStruct(u.Elem())
	case *types.Map:
		return anonStruct(u.Elem()) || anonStruct(u.Key())
	}
	return false
}

func demand(root string, pkgs []string) error {
	fset := token.NewFileSet()
	li := &localImporter{root: root, fset: fset, cache: map[string]*types.Package{}, infos: map[string]*types.Info{}, files: map[string][]*ast.File{}, std: importer.Default()}
	fmt.Println("pkg\tkind\tname\tloc\trefused_calls\tsupplied_calls\tlang_refusals\timported_types\tverdict")
	for _, path := range pkgs {
		if _, err := li.Import(path); err != nil {
			return err
		}
		info := li.infos[path]
		for _, f := range li.files[path] {
			for _, d := range f.Decls {
				fd, ok := d.(*ast.FuncDecl)
				if !ok {
					continue
				}
				kind, name := "func", fd.Name.Name
				if fd.Recv != nil {
					kind, name = "method", recvName(fd.Recv.List[0].Type)+"."+name
				}
				loc := fset.Position(fd.End()).Line - fset.Position(fd.Pos()).Line + 1
				refused, ok2, lang, itypes := demandSet{}, demandSet{}, demandSet{}, demandSet{}
				// Signature: imported generic instantiations here are
				// UNSTUBBABLE (whole-export kill: quarantinedMethodStub's
				// sigRefusal path) — recorded as a lang refusal.
				if obj, isFn := info.Defs[fd.Name].(*types.Func); isFn {
					sig := obj.Type().(*types.Signature)
					for _, tup := range []*types.Tuple{sig.Params(), sig.Results()} {
						for i := 0; i < tup.Len(); i++ {
							if k, g := importedNamed(tup.At(i).Type(), 0); k != "" {
								if g {
									lang.add("sig:imported-generic-inst:" + k)
								} else {
									itypes.add(k)
								}
							}
							if anonStruct(tup.At(i).Type()) {
								lang.add("FR-13:anon-struct-in-signature")
							}
						}
					}
				}
				if fd.Body == nil {
					continue
				}
				ast.Inspect(fd.Body, func(n ast.Node) bool {
					switch x := n.(type) {
					case *ast.CallExpr:
						switch fun := x.Fun.(type) {
						case *ast.Ident:
							if o, ok := info.Uses[fun].(*types.Builtin); ok && (o.Name() == "print" || o.Name() == "println") {
								refused.add("builtin." + o.Name())
							}
						case *ast.SelectorExpr:
							if id, ok := fun.X.(*ast.Ident); ok {
								if pn, ok := info.Uses[id].(*types.PkgName); ok && !isLocalPath(pn.Imported().Path()) {
									key := pn.Imported().Path() + "." + fun.Sel.Name
									if _, isType := info.Uses[fun.Sel].(*types.TypeName); isType {
										itypes.add(key) // conversion T(x)
										return true
									}
									if _, ok := supplied[key]; ok {
										ok2.add(key)
									} else {
										refused.add(key)
									}
									return true
								}
							}
							if sel, ok := info.Selections[fun]; ok && sel.Kind() == types.MethodVal {
								recv := sel.Recv()
								if p, isP := recv.(*types.Pointer); isP {
									recv = p.Elem()
								}
								if nm, isN := recv.(*types.Named); isN && nm.Obj().Pkg() != nil && !isLocalPath(nm.Obj().Pkg().Path()) {
									key := nm.Obj().Pkg().Path() + "." + nm.Obj().Name() + "." + fun.Sel.Name
									if _, ok := supplied[key]; ok {
										ok2.add(key)
									} else {
										refused.add(key)
									}
								}
							}
						}
					case *ast.RangeStmt:
						if tv, ok := info.Types[x.X]; ok {
							if _, isSig := tv.Type.Underlying().(*types.Signature); isSig {
								lang.add("FR-12:range-over-func")
							}
						}
					case *ast.GoStmt:
						lang.add("go-statement")
					case *ast.CompositeLit:
						if tv, ok := info.Types[x]; ok && anonStruct(tv.Type) {
							if _, isNamed := tv.Type.(*types.Named); !isNamed {
								lang.add("FR-13:anon-struct-literal")
							}
						}
					case *ast.StructType:
						if x.Fields != nil && len(x.Fields.List) > 0 {
							lang.add("FR-13:anon-struct-type")
						}
					case *ast.BasicLit:
						if x.Kind == token.IMAG {
							lang.add("FR-15:complex")
						}
					case *ast.BranchStmt:
						if x.Tok == token.GOTO {
							lang.add("goto(FR-11/20 shapes only)")
						}
					}
					// Imported named types flowing through expressions.
					if e, isExpr := n.(ast.Expr); isExpr {
						if tv, ok := info.Types[e]; ok && tv.Type != nil {
							if k, g := importedNamed(tv.Type, 0); k != "" {
								if g {
									lang.add("imported-generic-inst:" + k)
								} else {
									itypes.add(k)
								}
							}
						}
					}
					return true
				})
				verdict := "lowers(static)"
				if len(refused) > 0 || len(lang) > 0 {
					verdict = "refused(static)"
				}
				fmt.Printf("%s\t%s\t%s\t%d\t%s\t%s\t%s\t%s\t%s\n", path, kind, name, loc, refused.sorted(), ok2.sorted(), lang.sorted(), itypes.sorted(), verdict)
			}
		}
	}
	_ = os.Stderr
	return nil
}
