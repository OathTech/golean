package main

// static.go — the STATIC pass: go/types over the program and its transitive
// case-local imports (the same loader shape as tools/nativefrontend/load.go:
// a directory <root>/<path> is a local package, everything else is stdlib
// through the host's export data), then for EVERY declaration the set of
// refused demands it makes, judged against the supply tables (causes.go).
//
// Measured direction (calibration against the frontend's own wires,
// docs/2026-09-04_lower-diagnose.md §5): an UNDER-approximation of "would
// the frontend quarantine this declaration" — the rules that fire are exact
// (0 false positives after the audit fix round), and what the pass does not
// judge is disclosed PER RUN in the report's "not judged statically"
// section (fmt's verb×kind matrix, mono.go's stencil-time refusals, …).
// Shape-dependent refusals are reported as MAY-REFUSE (the goto hoisting
// shapes, non-reserved build tags).

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

type finding struct {
	Cause   *cause
	Key     string
	Pos     string
	Certain bool // false = shape-dependent (may-refuse)
	Export  bool // this site is a WHOLE-EXPORT refusal today
	Call    bool // the DECLARATION lowers; the CALL refuses when reached (a library-side quarantine or a D5 stub)
}

type declReport struct {
	Pkg, Kind, Name string
	Pos             string
	LOC             int
	Findings        []finding // deduped by (cause id, key)
	Supplied        []string  // "key (class)" — stdlib demands that lower today
	ImportedTypes   []string  // opaque D5 markers (not blockers by themselves)
	GenericSites    int       // type parameters declared + instantiation sites (mono.go's stencil-time refusals are not judged here)
	IsGeneric       bool      // declares type parameters: a TEMPLATE, quarantined by design, stenciled per instantiation
	usedVars        map[types.Object]bool
	fkeys           map[string]bool
	skeys           map[string]bool
	tkeys           map[string]bool
}

func (d *declReport) add(f finding) {
	if d.fkeys == nil {
		d.fkeys = map[string]bool{}
	}
	k := f.Cause.ID + "\x00" + f.Key
	if prev, ok := d.fkeys[k]; ok && prev {
		// keep the strongest scope/certainty
		for i := range d.Findings {
			if d.Findings[i].Cause.ID == f.Cause.ID && d.Findings[i].Key == f.Key {
				d.Findings[i].Export = d.Findings[i].Export || f.Export
				d.Findings[i].Certain = d.Findings[i].Certain || f.Certain
				d.Findings[i].Call = d.Findings[i].Call && f.Call
			}
		}
		return
	}
	d.fkeys[k] = true
	d.Findings = append(d.Findings, f)
}

func (d *declReport) supplied(key, class string) {
	if d.skeys == nil {
		d.skeys = map[string]bool{}
	}
	s := key + " (" + class + ")"
	if !d.skeys[s] {
		d.skeys[s] = true
		d.Supplied = append(d.Supplied, s)
	}
}

func (d *declReport) importedType(key string) {
	if d.tkeys == nil {
		d.tkeys = map[string]bool{}
	}
	if !d.tkeys[key] {
		d.tkeys[key] = true
		d.ImportedTypes = append(d.ImportedTypes, key)
	}
}

func (d *declReport) certainFindings() []finding {
	var out []finding
	for _, f := range d.Findings {
		if f.Certain {
			out = append(out, f)
		}
	}
	return out
}

// declRefusals: the certain findings that refuse THIS declaration (scope
// decl/export) — `call`-scoped findings (an imported type's D5 stub) leave
// the declaration lowered and refuse when the call is reached.
func (d *declReport) declRefusals() []finding {
	var out []finding
	for _, f := range d.Findings {
		if f.Certain && !f.isCall() {
			out = append(out, f)
		}
	}
	return out
}

func (f finding) isCall() bool { return f.Call || f.Cause.Scope == "call" }

func (d *declReport) verdict() string {
	certain, may := 0, 0
	for _, f := range d.Findings {
		if f.Certain {
			certain++
		} else {
			may++
		}
	}
	switch {
	case certain > 0:
		return "refused(static)"
	case may > 0:
		return "may-refuse(static)"
	}
	return "lowers(static)"
}

func (d *declReport) exportKill() bool {
	for _, f := range d.Findings {
		if f.Certain && f.Export {
			return true
		}
	}
	return false
}

type localPkg struct {
	path    string // "main" for the main package
	dir     string
	files   []*ast.File
	pkg     *types.Package
	info    *types.Info
	imports []string // local imports
	decls   []*declReport
}

type program struct {
	root     string
	fset     *token.FileSet
	sup      *supply
	std      types.Importer
	pkgs     map[string]*localPkg
	order    []string // load order (dependencies first), main last
	typeErrs []string
	loading  map[string]bool
	varDecls map[types.Object]*declReport // package-level vars of local packages -> their declaration
}

// loadProgram loads the main package at root, its transitive case-local
// imports, and every `includes` path (a case-local package the main
// package does not import — the census's extra roots).
func loadProgram(root string, sup *supply, includes ...string) (*program, error) {
	fi, err := os.Stat(root)
	if err != nil {
		return nil, err
	}
	if !fi.IsDir() {
		if filepath.Ext(root) != ".go" {
			return nil, fmt.Errorf("target %s is neither a directory nor a .go file", root)
		}
		root = filepath.Dir(root)
	}
	p := &program{root: root, fset: token.NewFileSet(), sup: sup, std: importer.Default(),
		pkgs: map[string]*localPkg{}, loading: map[string]bool{}, varDecls: map[types.Object]*declReport{}}
	if _, err := p.load("main", root); err != nil {
		return nil, err
	}
	for _, inc := range includes {
		if !p.isLocalPath(inc) {
			return nil, fmt.Errorf("--include %q: no case-local package directory %s", inc, filepath.Join(root, filepath.FromSlash(inc)))
		}
		if _, err := p.Import(inc); err != nil {
			return nil, err
		}
	}
	if len(p.typeErrs) > 0 {
		n := len(p.typeErrs)
		show := p.typeErrs
		if n > 8 {
			show = show[:8]
		}
		return nil, fmt.Errorf("the program does not type-check (%d error(s)); nothing to diagnose — the frontend would refuse before any lowering:\n  %s",
			n, strings.Join(show, "\n  "))
	}
	return p, nil
}

func nonTestGo(fi os.FileInfo) bool {
	n := fi.Name()
	return strings.HasSuffix(n, ".go") && !strings.HasSuffix(n, "_test.go")
}

func (p *program) isLocalPath(path string) bool {
	if path == "main" {
		return false
	}
	dir := filepath.Join(p.root, filepath.FromSlash(path))
	ents, err := filepath.Glob(filepath.Join(dir, "*.go"))
	return err == nil && len(ents) > 0
}

// Import implements types.Importer: case-local directories first, the
// host export data for everything else (fail closed at type-check on an
// unknown path, as the frontend does).
func (p *program) Import(path string) (*types.Package, error) {
	if lp, ok := p.pkgs[path]; ok {
		return lp.pkg, nil
	}
	if p.isLocalPath(path) {
		if p.loading[path] {
			return nil, fmt.Errorf("import cycle among local packages at %q", path)
		}
		lp, err := p.load(path, filepath.Join(p.root, filepath.FromSlash(path)))
		if err != nil {
			return nil, err
		}
		return lp.pkg, nil
	}
	return p.std.Import(path)
}

func (p *program) load(path, dir string) (*localPkg, error) {
	p.loading[path] = true
	defer delete(p.loading, path)
	pkgs, err := parser.ParseDir(p.fset, dir, nonTestGo, parser.ParseComments)
	if err != nil {
		return nil, err
	}
	if len(pkgs) != 1 {
		return nil, fmt.Errorf("%s: expected exactly one package, found %d", dir, len(pkgs))
	}
	var apkg *ast.Package
	for _, ap := range pkgs {
		apkg = ap
	}
	// Directory-mode presentation order (file-name sort), as the frontend.
	names := make([]string, 0, len(apkg.Files))
	for n := range apkg.Files {
		names = append(names, n)
	}
	sort.Strings(names)
	lp := &localPkg{path: path, dir: dir}
	for _, n := range names {
		lp.files = append(lp.files, apkg.Files[n])
	}
	// Local imports first (dependencies before dependents), mirroring the
	// loader's discovery; a dotted local path is refused by the frontend
	// but we still LOAD it so the census sees through it.
	seen := map[string]bool{}
	for _, f := range lp.files {
		for _, im := range f.Imports {
			ip := strings.Trim(im.Path.Value, `"`)
			if p.isLocalPath(ip) && !seen[ip] {
				seen[ip] = true
				lp.imports = append(lp.imports, ip)
			}
		}
	}
	sort.Strings(lp.imports)
	for _, ip := range lp.imports {
		if _, ok := p.pkgs[ip]; !ok {
			if _, err := p.Import(ip); err != nil {
				return nil, err
			}
		}
	}
	info := &types.Info{
		Types: map[ast.Expr]types.TypeAndValue{}, Defs: map[*ast.Ident]types.Object{},
		Uses: map[*ast.Ident]types.Object{}, Selections: map[*ast.SelectorExpr]*types.Selection{},
		Implicits: map[ast.Node]types.Object{}, Instances: map[*ast.Ident]types.Instance{},
		Scopes: map[ast.Node]*types.Scope{},
	}
	conf := types.Config{Importer: p, Error: func(e error) { p.typeErrs = append(p.typeErrs, e.Error()) }}
	tpkg, _ := conf.Check(path, p.fset, lp.files, info)
	lp.pkg = tpkg
	lp.info = info
	p.pkgs[path] = lp
	p.order = append(p.order, path)
	return lp, nil
}

func (p *program) pos(n ast.Node) string {
	ps := p.fset.Position(n.Pos())
	rel, err := filepath.Rel(p.root, ps.Filename)
	if err != nil || strings.HasPrefix(rel, "..") {
		rel = filepath.Base(ps.Filename)
	}
	return fmt.Sprintf("%s:%d", filepath.ToSlash(rel), ps.Line)
}

func (p *program) isLocalPkg(tp *types.Package) bool {
	if tp == nil {
		return false
	}
	_, ok := p.pkgs[tp.Path()]
	return ok
}

// ---- the declaration census -----------------------------------------------

func (p *program) census() {
	for _, path := range p.order {
		lp := p.pkgs[path]
		a := &analyzer{p: p, lp: lp, info: lp.info}
		a.run()
	}
	// quarantine-cascade: a declaration that READS a package-level variable
	// whose own declaration is refused per declaration (a poisoned cell —
	// H-11 seeds it and every reader refuses by name).
	for _, path := range p.order {
		for _, d := range p.pkgs[path].decls {
			for obj := range d.usedVars {
				vd := p.varDecls[obj]
				// An export-killed var poisons nothing: the whole export refuses
				// today (the cascade is the PER-DECLARATION poisoning's shape).
				if vd == nil || vd == d || len(vd.declRefusals()) == 0 || vd.exportKill() {
					continue
				}
				d.add(finding{Cause: mustCause("quarantine-cascade"), Key: vd.Pkg + "." + obj.Name(), Pos: d.Pos, Certain: true})
			}
		}
	}
}

type analyzer struct {
	p    *program
	lp   *localPkg
	info *types.Info
	// per-package: function-local type names for FR-19
	localTypes map[string][]*declReport
	pkgTypes   map[string]bool
}

func typeStr(t types.Type) string {
	s := types.TypeString(t, func(pk *types.Package) string { return pk.Name() })
	if len(s) > 60 {
		s = s[:57] + "..."
	}
	return s
}

func (a *analyzer) run() {
	a.localTypes = map[string][]*declReport{}
	a.pkgTypes = map[string]bool{}
	for _, f := range a.lp.files {
		for _, d := range f.Decls {
			if gd, ok := d.(*ast.GenDecl); ok && gd.Tok == token.TYPE {
				for _, s := range gd.Specs {
					a.pkgTypes[s.(*ast.TypeSpec).Name.Name] = true
				}
			}
		}
	}
	for _, f := range a.lp.files {
		a.fileLevel(f)
		for _, d := range f.Decls {
			switch x := d.(type) {
			case *ast.FuncDecl:
				a.funcDecl(x)
			case *ast.GenDecl:
				a.genDecl(x, nil)
			}
		}
	}
	// FR-19: duplicate function-local TypeIds (two locals of one name, or
	// a local shadowing a package-level type).
	names := make([]string, 0, len(a.localTypes))
	for n := range a.localTypes {
		names = append(names, n)
	}
	sort.Strings(names)
	for _, n := range names {
		ds := a.localTypes[n]
		if len(ds) > 1 || a.pkgTypes[n] {
			for _, d := range ds {
				d.add(finding{Cause: mustCause("duplicate-typeid"), Key: n, Pos: d.Pos, Certain: true, Export: true})
			}
		}
	}
}

// fileLevel: import shapes and build constraints — package-level refusals
// attributed to a pseudo-declaration `file <name>`.
func (a *analyzer) fileLevel(f *ast.File) {
	var d *declReport
	get := func() *declReport {
		if d == nil {
			d = &declReport{Pkg: a.lp.path, Kind: "file", Name: filepath.Base(a.p.fset.Position(f.Pos()).Filename), Pos: a.p.pos(f)}
			a.lp.decls = append(a.lp.decls, d)
		}
		return d
	}
	for _, cg := range f.Comments {
		if cg.Pos() > f.Package {
			break
		}
		for _, c := range cg.List {
			if strings.HasPrefix(c.Text, "//go:build ") {
				expr := strings.TrimSpace(strings.TrimPrefix(c.Text, "//go:build "))
				get().add(finding{Cause: mustCause("build-constraint"), Key: expr, Pos: a.p.pos(c), Certain: reservedTag(expr), Export: true})
			}
		}
	}
	for _, im := range f.Imports {
		ip := strings.Trim(im.Path.Value, `"`)
		local := a.p.isLocalPath(ip)
		switch {
		case local && strings.Contains(ip, "."):
			get().add(finding{Cause: mustCause("local-import-shape"), Key: "dotted path " + ip, Pos: a.p.pos(im), Certain: true, Export: true})
		case local && im.Name != nil && im.Name.Name == ".":
			get().add(finding{Cause: mustCause("local-import-shape"), Key: "dot import " + ip, Pos: a.p.pos(im), Certain: true, Export: true})
		case ip == "main":
			get().add(finding{Cause: mustCause("local-import-shape"), Key: "reserved path main", Pos: a.p.pos(im), Certain: true, Export: true})
		case !local && im.Name != nil && im.Name.Name == "." && ip == "unsafe":
			get().add(finding{Cause: mustCause("unsafe"), Key: "import . unsafe", Pos: a.p.pos(im), Certain: true})
		}
	}
}

var reservedTags = []string{"linux", "darwin", "windows", "freebsd", "netbsd", "openbsd", "plan9", "solaris", "aix", "js", "wasip1", "android", "ios",
	"amd64", "arm64", "386", "arm", "ppc64", "ppc64le", "mips", "mipsle", "mips64", "mips64le", "riscv64", "s390x", "wasm", "loong64",
	"cgo", "gc", "gccgo", "unix", "purego", "race", "msan", "asan", "ignore"}

func reservedTag(expr string) bool {
	for _, tok := range strings.FieldsFunc(expr, func(r rune) bool { return r == ' ' || r == '(' || r == ')' || r == '!' || r == '&' || r == '|' }) {
		if strings.HasPrefix(tok, "go1.") {
			return true
		}
		for _, r := range reservedTags {
			if tok == r {
				return true
			}
		}
	}
	return false
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

func (a *analyzer) newDecl(kind, name string, n ast.Node) *declReport {
	d := &declReport{Pkg: a.lp.path, Kind: kind, Name: name, Pos: a.p.pos(n),
		LOC: a.p.fset.Position(n.End()).Line - a.p.fset.Position(n.Pos()).Line + 1}
	a.lp.decls = append(a.lp.decls, d)
	return d
}

func (a *analyzer) funcDecl(fd *ast.FuncDecl) {
	// The main package's `main` is never emitted by the frontend
	// (emit.go emitProgram skips it; drivers run named entry functions),
	// so nothing in its body can block a lowering — not a declaration of
	// the census (said in the report's notes).
	if a.lp.path == "main" && fd.Recv == nil && fd.Name.Name == "main" {
		return
	}
	kind, name := "func", fd.Name.Name
	isMethod := fd.Recv != nil
	if isMethod {
		kind, name = "method", recvName(fd.Recv.List[0].Type)+"."+name
	}
	d := a.newDecl(kind, name, fd)
	if fd.Type.TypeParams != nil && len(fd.Type.TypeParams.List) > 0 {
		d.GenericSites++
		d.IsGeneric = true
	}
	// Signature: a type that does not lower makes a METHOD unstubbable
	// (export kill, FR-23's sigRefusal arm) — EXCEPT the opaque-marker
	// classes, which stub per declaration: imported generic instantiations
	// (FR-23) and, since lane fr24 (2026-09-04), unlowerable basic types
	// (FR-25: complex64/complex128/unsafe.Pointer). A func quarantines with
	// an arity-only stub.
	if obj, ok := a.info.Defs[fd.Name].(*types.Func); ok {
		sig := obj.Type().(*types.Signature)
		tuples := []*types.Tuple{sig.Params(), sig.Results()}
		for _, tup := range tuples {
			for i := 0; i < tup.Len(); i++ {
				for _, f := range a.typeFindings(tup.At(i).Type(), fd.Type, d) {
					if f.Cause.ID == "imported-generic-inst" && isMethod {
						f = finding{Cause: mustCause("imported-generic-sig"), Key: f.Key, Pos: f.Pos, Certain: true}
					} else if isMethod && f.Cause.ID != "complex" && f.Cause.ID != "unsafe" {
						f.Export = true
					}
					d.add(f)
				}
			}
		}
	}
	if fd.Body == nil {
		return
	}
	// init() runs before every subject, so the frontend emits it WITHOUT a
	// per-declaration quarantine: an unsupported init body refuses the
	// WHOLE export (emit.go emitProgram, design note §2). Every certain
	// finding inside one is export-scoped.
	isInit := fd.Recv == nil && fd.Name.Name == "init"
	before := len(d.Findings)
	defer func() {
		if !isInit {
			return
		}
		for i := before; i < len(d.Findings); i++ {
			if d.Findings[i].Certain {
				d.Findings[i].Export = true
			}
		}
	}()
	// Function-local types (FR-19).
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		if gd, ok := n.(*ast.GenDecl); ok && gd.Tok == token.TYPE {
			for _, s := range gd.Specs {
				ts := s.(*ast.TypeSpec)
				a.localTypes[ts.Name.Name] = append(a.localTypes[ts.Name.Name], d)
			}
		}
		return true
	})
	a.body(d, fd.Body, fd)
}

func (a *analyzer) genDecl(gd *ast.GenDecl, enclosing *declReport) {
	for _, s := range gd.Specs {
		switch sp := s.(type) {
		case *ast.TypeSpec:
			d := enclosing
			if d == nil {
				d = a.newDecl("type", sp.Name.Name, sp)
			}
			// The declared type's own structure: anonymous structs / complex
			// / unmodeled imported types INSIDE it (not the top-level struct
			// itself, which is the named type).
			if obj, ok := a.info.Defs[sp.Name].(*types.TypeName); ok {
				if named, ok := obj.Type().(*types.Named); ok {
					a.typeInside(named.Underlying(), sp, d)
				}
			}
		case *ast.ValueSpec:
			names := make([]string, 0, len(sp.Names))
			for _, n := range sp.Names {
				names = append(names, n.Name)
			}
			d := enclosing
			if d == nil {
				kind := "var"
				if gd.Tok == token.CONST {
					kind = "const"
				}
				d = a.newDecl(kind, strings.Join(names, ","), sp)
			}
			// The variable's TYPE (package level: since lane fr24, 2026-09-04,
			// an unlowerable type POISONS the var per declaration at
			// collectGlobals — FR-24's shape, decl-scoped; the readers
			// quarantine by name).
			for _, n := range sp.Names {
				if obj := a.info.Defs[n]; obj != nil {
					if enclosing == nil && gd.Tok == token.VAR {
						a.p.varDecls[obj] = d
					}
					fs := a.typeFindings(obj.Type(), sp, d)
					for _, f := range fs {
						if enclosing == nil && gd.Tok == token.VAR {
							d.add(finding{Cause: mustCause("global-type-unlowerable"), Key: n.Name + " " + typeStr(obj.Type()), Pos: f.Pos, Certain: f.Certain})
						}
						d.add(f)
					}
				}
			}
			// The initializer.
			before := len(d.Findings)
			for _, v := range sp.Values {
				a.body(d, v, nil)
			}
			if enclosing == nil && gd.Tok == token.VAR && len(sp.Values) > 0 {
				a.initializerScope(d, sp, before)
			}
		}
	}
}

// initializerScope: H-11 (emit.go quarantineUnlowerableGlobals /
// initializerEffectIsolated): an initializer that does not lower is
// quarantined PER DECLARATION only if its expression is effect-isolated —
// a positive allowlist in which the only admitted calls are
// pureUnmodeledCallees. Any other call in a refused initializer = whole
// export (FR-22). Other non-isolated shapes (index, deref, receive, …)
// are not tracked here — the scope is UNDER-reported for them, said so.
func (a *analyzer) initializerScope(d *declReport, sp *ast.ValueSpec, before int) {
	if len(d.Findings) == before {
		return
	}
	var callee string
	for _, v := range sp.Values {
		ast.Inspect(v, func(n ast.Node) bool {
			if _, isLit := n.(*ast.FuncLit); isLit {
				return false // a closure is a value, not a call
			}
			c, ok := n.(*ast.CallExpr)
			if !ok || callee != "" {
				return true
			}
			if tv, ok := a.info.Types[c.Fun]; ok && tv.IsType() {
				return true // conversion
			}
			key := a.callKey(c)
			if a.p.sup.initCallee[key] {
				return true
			}
			callee = key
			return false
		})
	}
	if callee == "" {
		return
	}
	for i := before; i < len(d.Findings); i++ {
		d.Findings[i].Export = true
	}
	d.add(finding{Cause: mustCause("init-callee-unmodeled"), Key: callee, Pos: d.Pos, Certain: true, Export: true})
}

// callKey renders a call's callee for the initializer allowlist:
// "pkg.Member" for a stdlib selector, the identifier otherwise.
func (a *analyzer) callKey(c *ast.CallExpr) string {
	switch fun := c.Fun.(type) {
	case *ast.SelectorExpr:
		if id, ok := fun.X.(*ast.Ident); ok {
			if pn, ok := a.info.Uses[id].(*types.PkgName); ok {
				return pn.Imported().Path() + "." + fun.Sel.Name
			}
		}
		return "." + fun.Sel.Name
	case *ast.Ident:
		return fun.Name
	}
	return fmt.Sprintf("%T", c.Fun)
}

// typeInside: findings for the STRUCTURE of a declared type (fields,
// elements), skipping the top-level named/struct itself.
func (a *analyzer) typeInside(u types.Type, at ast.Node, d *declReport) {
	switch t := u.(type) {
	case *types.Struct:
		for i := 0; i < t.NumFields(); i++ {
			for _, f := range a.typeFindings(t.Field(i).Type(), at, d) {
				d.add(f)
			}
		}
	case *types.Interface:
		// method signatures
		for i := 0; i < t.NumMethods(); i++ {
			for _, f := range a.typeFindings(t.Method(i).Type(), at, d) {
				d.add(f)
			}
		}
	default:
		for _, f := range a.typeFindings(u, at, d) {
			d.add(f)
		}
	}
}

// typeFindings: the refusals a TYPE carries (recursively), plus the
// opaque imported markers recorded on d. Never flags a local named type
// (its own declaration is judged separately) or a type parameter (a
// generic template's quarantine is by design).
func (a *analyzer) typeFindings(t types.Type, at ast.Node, d *declReport) []finding {
	var out []finding
	seen := map[types.Type]bool{}
	pos := a.p.pos(at)
	var walk func(t types.Type, depth int)
	walk = func(t types.Type, depth int) {
		if t == nil || depth > 8 || seen[t] {
			return
		}
		seen[t] = true
		switch u := t.(type) {
		case *types.Basic:
			switch u.Kind() {
			case types.Complex64, types.Complex128, types.UntypedComplex:
				out = append(out, finding{Cause: mustCause("complex"), Key: u.String(), Pos: pos, Certain: true})
			}
		case *types.Alias:
			walk(types.Unalias(u), depth+1)
		case *types.Named:
			obj := u.Obj()
			if obj.Pkg() == nil {
				return // universe (error, comparable)
			}
			if u.TypeArgs() != nil {
				for i := 0; i < u.TypeArgs().Len(); i++ {
					walk(u.TypeArgs().At(i), depth+1)
				}
			}
			if a.p.isLocalPkg(obj.Pkg()) {
				return
			}
			path, name := obj.Pkg().Path(), obj.Name()
			switch {
			case path == "sync":
				if !a.p.sup.syncType["sync."+name] {
					id := "sync-unmodeled"
					if name == "Cond" {
						id = "sync-cond"
					}
					out = append(out, finding{Cause: mustCause(id), Key: "sync." + name, Pos: pos, Certain: true})
				}
			case path == "sync/atomic":
				if !a.p.sup.shadowType["sync/atomic."+name] {
					out = append(out, finding{Cause: mustCause("atomic-unmodeled"), Key: "sync/atomic." + name, Pos: pos, Certain: true})
				}
			case u.TypeArgs() != nil && u.TypeArgs().Len() > 0:
				if !a.p.sup.sourceThrough[path] {
					out = append(out, finding{Cause: mustCause("imported-generic-inst"), Key: path + "." + name, Pos: pos, Certain: true})
				}
			case path == "unsafe":
				out = append(out, finding{Cause: mustCause("unsafe"), Key: "unsafe." + name, Pos: pos, Certain: true})
			case path == "reflect" || path == "internal/reflectlite":
				out = append(out, finding{Cause: mustCause("reflect"), Key: path + "." + name, Pos: pos, Certain: true})
			default:
				if _, isIface := u.Underlying().(*types.Interface); !isIface {
					d.importedType(path + "." + name)
				}
			}
		case *types.Struct:
			if u.NumFields() > 0 {
				out = append(out, finding{Cause: mustCause("anon-struct"), Key: typeStr(u), Pos: pos, Certain: true})
			}
			for i := 0; i < u.NumFields(); i++ {
				walk(u.Field(i).Type(), depth+1)
			}
		case *types.Pointer:
			walk(u.Elem(), depth+1)
		case *types.Slice:
			walk(u.Elem(), depth+1)
		case *types.Array:
			walk(u.Elem(), depth+1)
		case *types.Chan:
			walk(u.Elem(), depth+1)
		case *types.Map:
			walk(u.Key(), depth+1)
			walk(u.Elem(), depth+1)
		case *types.Signature:
			for i := 0; i < u.Params().Len(); i++ {
				walk(u.Params().At(i).Type(), depth+1)
			}
			for i := 0; i < u.Results().Len(); i++ {
				walk(u.Results().At(i).Type(), depth+1)
			}
		case *types.Tuple:
			for i := 0; i < u.Len(); i++ {
				walk(u.At(i).Type(), depth+1)
			}
		case *types.Interface, *types.TypeParam, *types.Union:
			// interfaces are structural identities; type params are by design
		}
	}
	walk(t, 0)
	return out
}

// stdlibSel: `pkg.Member` where pkg names a NON-local package.
func (a *analyzer) stdlibSel(sel *ast.SelectorExpr) (path string, member string, obj types.Object, ok bool) {
	id, isId := sel.X.(*ast.Ident)
	if !isId {
		return "", "", nil, false
	}
	pn, isPkg := a.info.Uses[id].(*types.PkgName)
	if !isPkg || a.p.isLocalPkg(pn.Imported()) {
		return "", "", nil, false
	}
	return pn.Imported().Path(), sel.Sel.Name, a.info.Uses[sel.Sel], true
}

// classifyPkgCall judges a direct call `pkg.Member(...)` on a stdlib package.
func (a *analyzer) classifyPkgCall(d *declReport, path, member string, at ast.Node) {
	key := path + "." + member
	pos := a.p.pos(at)
	sup := a.p.sup
	switch {
	case path == "unsafe":
		d.add(finding{Cause: mustCause("unsafe"), Key: key, Pos: pos, Certain: true})
	case path == "reflect" || path == "internal/reflectlite":
		d.add(finding{Cause: mustCause("reflect"), Key: key, Pos: pos, Certain: true})
	case path == "sync":
		d.add(finding{Cause: mustCause("sync-unmodeled"), Key: key, Pos: pos, Certain: true})
	case path == "sync/atomic":
		if sup.atomicModeled(member) {
			d.supplied(key, "machine atomic-op")
		} else {
			d.add(finding{Cause: mustCause("atomic-unmodeled"), Key: key, Pos: pos, Certain: true})
		}
	case sup.intercept[key]:
		d.supplied(key, "intercept")
	case sup.sourceThrough[path]:
		if lr, ok := sup.libRefused[key]; ok {
			// The library function itself is quarantined (FR-21 / reflect);
			// this declaration LOWERS and the call refuses when reached.
			d.add(finding{Cause: mustCause(lr.Cause), Key: key, Pos: pos, Certain: true, Call: true})
		} else {
			d.supplied(key, "source-through")
		}
	case sup.shim[key] != "":
		d.supplied(key, "shim")
	case sup.shimPackage(path):
		d.add(finding{Cause: mustCause("stdlib-member-unmodeled"), Key: key, Pos: pos, Certain: true})
	default:
		d.add(finding{Cause: mustCause("stdlib-package-unmodeled"), Key: key, Pos: pos, Certain: true})
	}
}

// classifyMethod judges a method value/call on an IMPORTED named receiver.
func (a *analyzer) classifyMethod(d *declReport, recv types.Type, method string, at ast.Node) {
	if p, ok := recv.(*types.Pointer); ok {
		recv = p.Elem()
	}
	recv = types.Unalias(recv)
	nm, ok := recv.(*types.Named)
	if !ok || nm.Obj().Pkg() == nil || a.p.isLocalPkg(nm.Obj().Pkg()) {
		return
	}
	if _, isIface := nm.Underlying().(*types.Interface); isIface {
		return // dynamic dispatch over an interface identity — the concrete value's origin is the blocker
	}
	path, tname := nm.Obj().Pkg().Path(), nm.Obj().Name()
	key := path + "." + tname + "." + method
	pos := a.p.pos(at)
	sup := a.p.sup
	switch {
	case path == "sync":
		if sup.syncOp[key] {
			d.supplied(key, "machine sync-op")
		} else if tname == "Cond" {
			d.add(finding{Cause: mustCause("sync-cond"), Key: key, Pos: pos, Certain: true})
		} else {
			d.add(finding{Cause: mustCause("sync-unmodeled"), Key: key, Pos: pos, Certain: true})
		}
	case path == "sync/atomic":
		if sup.shadowType[path+"."+tname] && sup.atomicModeled(method) {
			d.supplied(key, "machine atomic-op")
		} else {
			d.add(finding{Cause: mustCause("atomic-unmodeled"), Key: key, Pos: pos, Certain: true})
		}
	case sup.sourceThrough[path]:
		if lr, ok := sup.libRefused[key]; ok {
			d.add(finding{Cause: mustCause(lr.Cause), Key: key, Pos: pos, Certain: true, Call: true})
		} else {
			d.supplied(key, "source-through")
		}
	case path == "reflect" || path == "internal/reflectlite":
		d.add(finding{Cause: mustCause("reflect"), Key: key, Pos: pos, Certain: true})
	default:
		d.add(finding{Cause: mustCause("stdlib-type-method"), Key: key, Pos: pos, Certain: true})
	}
}

func isBuiltin(a *analyzer, e ast.Expr) (string, bool) {
	id, ok := e.(*ast.Ident)
	if !ok {
		return "", false
	}
	if b, ok := a.info.Uses[id].(*types.Builtin); ok {
		return b.Name(), true
	}
	return "", false
}

// body: the statement/expression walk over one declaration's code.
func (a *analyzer) body(d *declReport, root ast.Node, fd *ast.FuncDecl) {
	// Labels at the function body's top level (goto shape check).
	topLabels := map[string]bool{}
	if fd != nil && fd.Body != nil {
		for _, s := range fd.Body.List {
			if ls, ok := s.(*ast.LabeledStmt); ok {
				topLabels[ls.Label.Name] = true
			}
		}
	}
	var stack []ast.Node
	ast.Inspect(root, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		stack = append(stack, n)
		pos := a.p.pos(n)
		switch x := n.(type) {
		case *ast.GenDecl:
			// nested declarations (local types/vars) — analyzed in place
			if x.Tok == token.TYPE {
				a.genDecl(x, d)
				return false
			}
		case *ast.CallExpr:
			if name, ok := isBuiltin(a, x.Fun); ok {
				switch name {
				case "print", "println":
					// Stdlib slice 3 (2026-09-04): print/println LOWER
					// (emitPrintStmt) for bool/integer/string operands; the
					// static verdict mirrors the emitter's refusals exactly —
					// zero operands (FR-29), float/complex operands (FR-29),
					// every other kind (address-printing; ledger §5.1 item 3).
					if len(x.Args) == 0 {
						d.add(finding{Cause: mustCause("print-zero-operands"), Key: name, Pos: pos, Certain: true})
						break
					}
					for _, arg := range x.Args {
						tv, ok := a.info.Types[arg]
						if !ok || tv.Type == nil {
							continue
						}
						b, isBasic := tv.Type.Underlying().(*types.Basic)
						switch {
						case !isBasic || b.Kind() == types.UnsafePointer:
							d.add(finding{Cause: mustCause("print-builtin"), Key: name, Pos: pos, Certain: true})
						case b.Info()&(types.IsFloat|types.IsComplex) != 0:
							d.add(finding{Cause: mustCause("print-float"), Key: name, Pos: pos, Certain: true})
						case b.Kind() == types.Bool, b.Kind() == types.String, b.Info()&types.IsInteger != 0:
							// admitted
						default:
							d.add(finding{Cause: mustCause("print-builtin"), Key: name, Pos: pos, Certain: true})
						}
					}
				case "real", "imag", "complex":
					d.add(finding{Cause: mustCause("complex"), Key: "builtin " + name, Pos: pos, Certain: true})
				}
				break
			}
			if tv, ok := a.info.Types[x.Fun]; ok && tv.IsType() {
				break // conversion — the type scan covers it
			}
			if sel, ok := x.Fun.(*ast.SelectorExpr); ok {
				if path, member, obj, ok := a.stdlibSel(sel); ok {
					if _, isType := obj.(*types.TypeName); !isType {
						a.classifyPkgCall(d, path, member, x)
						// (slices.Sort's element-kind check — the sortSlice
						// MACHINE OP's integer-kinds-only intercept — was
						// here until 2026-09-04; RETIRED with the op by memo
						// §3 row M, lane fr4-rowm: slices.Sort is a
						// source-through member like the rest of `slices`,
						// judged by classifyPkgCall's source-through arm.)
					}
					break
				}
				if s, ok := a.info.Selections[sel]; ok && s.Kind() == types.MethodVal {
					a.classifyMethod(d, s.Recv(), sel.Sel.Name, x)
				}
			}
		case *ast.SelectorExpr:
			// Value-position stdlib selectors (not the Fun of a call — the
			// parent check below) and method values / expressions.
			parentIsCallFun := false
			if len(stack) >= 2 {
				if c, ok := stack[len(stack)-2].(*ast.CallExpr); ok && c.Fun == x {
					parentIsCallFun = true
				}
			}
			if path, member, obj, ok := a.stdlibSel(x); ok {
				if parentIsCallFun {
					break
				}
				key := path + "." + member
				switch obj.(type) {
				case *types.Var:
					switch {
					case a.p.sup.sourceThrough[path]:
						d.supplied(key, "source-through var")
					case path == "unsafe":
						d.add(finding{Cause: mustCause("unsafe"), Key: key, Pos: pos, Certain: true})
					default:
						d.add(finding{Cause: mustCause("stdlib-var-unmodeled"), Key: key, Pos: pos, Certain: true})
					}
				case *types.Func:
					if a.p.sup.sourceThrough[path] {
						d.supplied(key, "source-through func value")
					} else {
						d.add(finding{Cause: mustCause("stdlib-value-position"), Key: key, Pos: pos, Certain: true})
					}
				}
				break
			}
			if s, ok := a.info.Selections[x]; ok {
				switch s.Kind() {
				case types.MethodVal:
					if !parentIsCallFun {
						if a.syncRecv(s.Recv()) {
							d.add(finding{Cause: mustCause("sync-value-shape"), Key: "method value " + typeStr(s.Recv()) + "." + x.Sel.Name, Pos: pos, Certain: true})
						} else {
							a.classifyMethod(d, s.Recv(), x.Sel.Name, x)
						}
					}
				case types.MethodExpr:
					// (*T).Mv over a value-receiver method — the deref adapter.
					if fn, ok := s.Obj().(*types.Func); ok {
						if rsig, ok := fn.Type().(*types.Signature); ok && rsig.Recv() != nil {
							if _, recvIsPtr := s.Recv().(*types.Pointer); recvIsPtr {
								if _, methodRecvPtr := rsig.Recv().Type().(*types.Pointer); !methodRecvPtr {
									d.add(finding{Cause: mustCause("method-expr-deref"), Key: "(*" + typeStr(s.Recv().(*types.Pointer).Elem()) + ")." + x.Sel.Name, Pos: pos, Certain: true})
								}
							}
						}
					}
					if a.syncRecv(s.Recv()) {
						d.add(finding{Cause: mustCause("sync-value-shape"), Key: "method expression " + typeStr(s.Recv()) + "." + x.Sel.Name, Pos: pos, Certain: true})
					} else {
						a.classifyMethod(d, s.Recv(), x.Sel.Name, x)
					}
				}
			}
		case *ast.RangeStmt:
			if tv, ok := a.info.Types[x.X]; ok && tv.Type != nil {
				if _, isSig := tv.Type.Underlying().(*types.Signature); isSig {
					d.add(finding{Cause: mustCause("range-over-func"), Key: typeStr(tv.Type), Pos: pos, Certain: true})
				}
			}
			if x.Tok == token.ASSIGN {
				for _, t := range []ast.Expr{x.Key, x.Value} {
					if t == nil {
						continue
					}
					if _, isId := t.(*ast.Ident); !isId {
						d.add(finding{Cause: mustCause("range-assign-nonident"), Key: "range assign", Pos: pos, Certain: true})
					}
				}
			}
		case *ast.GoStmt:
			if name, ok := isBuiltin(a, x.Call.Fun); ok {
				d.add(finding{Cause: mustCause("go-of-builtin"), Key: name, Pos: pos, Certain: true})
			}
			a.interceptedSpawn(d, "go", x.Call, pos)
		case *ast.DeferStmt:
			if name, ok := isBuiltin(a, x.Call.Fun); ok && name != "recover" && name != "close" {
				d.add(finding{Cause: mustCause("defer-of-builtin"), Key: name, Pos: pos, Certain: true})
			}
			a.interceptedSpawn(d, "defer", x.Call, pos)
		case *ast.CompositeLit:
			// A non-empty composite literal of a sync/atomic primitive (Q-SYNCLIT:
			// the empty literal is the zero value and lowers).
			if tv, ok := a.info.Types[x]; ok && tv.Type != nil && len(x.Elts) > 0 {
				if nm, ok := types.Unalias(tv.Type).(*types.Named); ok && nm.Obj().Pkg() != nil {
					if pp := nm.Obj().Pkg().Path(); pp == "sync" || pp == "sync/atomic" {
						d.add(finding{Cause: mustCause("sync-literal"), Key: pp + "." + nm.Obj().Name(), Pos: pos, Certain: true})
					}
				}
			}
		case *ast.Ident:
			if _, inst := a.info.Instances[x]; inst {
				d.GenericSites++
			}
			if v, ok := a.info.Uses[x].(*types.Var); ok && v.Pkg() != nil && a.p.isLocalPkg(v.Pkg()) && v.Parent() == v.Pkg().Scope() {
				if d.usedVars == nil {
					d.usedVars = map[types.Object]bool{}
				}
				d.usedVars[v] = true
			}
		case *ast.BranchStmt:
			if x.Tok == token.GOTO && x.Label != nil {
				if topLabels[x.Label.Name] {
					d.add(finding{Cause: mustCause("goto-hoist"), Key: x.Label.Name, Pos: pos, Certain: false})
				} else {
					d.add(finding{Cause: mustCause("goto-nested-label"), Key: x.Label.Name, Pos: pos, Certain: true})
				}
			}
		case *ast.BinaryExpr:
			if x.Op == token.LAND || x.Op == token.LOR {
				a.shortCircuit(d, x.Y)
			}
		case *ast.AssignStmt:
			if x.Tok == token.DEFINE && len(x.Rhs) == 1 {
				if call, isCall := x.Rhs[0].(*ast.CallExpr); isCall {
					for _, l := range x.Lhs {
						lid, ok := l.(*ast.Ident)
						if !ok || lid.Name == "_" || a.info.Defs[lid] == nil {
							continue
						}
						if a.readsOuter(call, lid.Name, a.info.Defs[lid]) {
							d.add(finding{Cause: mustCause("self-shadow-define"), Key: lid.Name, Pos: pos, Certain: true})
						}
					}
				}
			}
			if x.Tok == token.ASSIGN && len(x.Rhs) == 1 && len(x.Lhs) > 1 {
				if tv, ok := a.info.Types[x.Rhs[0]]; ok {
					if tup, ok := tv.Type.(*types.Tuple); ok && tup.Len() == len(x.Lhs) {
						for i, l := range x.Lhs {
							if id, ok := l.(*ast.Ident); ok && id.Name == "_" {
								continue
							}
							if ltv, ok := a.info.Types[l]; ok && ltv.Type != nil {
								if boxes(ltv.Type, tup.At(i).Type()) {
									d.add(finding{Cause: mustCause("tuple-iface-box"), Key: "assign " + typeStr(ltv.Type), Pos: pos, Certain: true})
								}
							}
						}
					}
				}
			}
		// NO ReturnStmt arm: `return two()` into interface results LOWERS (the
		// emitter destructures the tuple into $c0/$c1 with an explicit
		// to-interface box); FR-7's unsup exists only on the assign /
		// value-spec paths (emit.go 3018/3109/3421/3495). Audit fix round 2.
		case *ast.ValueSpec:
			if len(x.Values) == 1 && len(x.Names) > 1 {
				if tv, ok := a.info.Types[x.Values[0]]; ok {
					if tup, ok := tv.Type.(*types.Tuple); ok && tup.Len() == len(x.Names) {
						for i, nm := range x.Names {
							if obj := a.info.Defs[nm]; obj != nil && boxes(obj.Type(), tup.At(i).Type()) {
								d.add(finding{Cause: mustCause("tuple-iface-box"), Key: "var " + typeStr(obj.Type()), Pos: pos, Certain: true})
							}
						}
					}
				}
			}
		}
		// Every typed expression: the type scan (complex, anonymous structs,
		// imported generic instantiations, unmodeled sync/atomic types).
		if e, isExpr := n.(ast.Expr); isExpr {
			if tv, ok := a.info.Types[e]; ok && tv.Type != nil {
				if _, isTuple := tv.Type.(*types.Tuple); !isTuple || true {
					for _, f := range a.typeFindings(tv.Type, e, d) {
						d.add(f)
					}
				}
			}
		}
		return true
	})
}

// syncRecv: is t (or *t) one of the machine-owned sync primitives?
func (a *analyzer) syncRecv(t types.Type) bool {
	if p, ok := t.(*types.Pointer); ok {
		t = p.Elem()
	}
	nm, ok := types.Unalias(t).(*types.Named)
	return ok && nm.Obj().Pkg() != nil && nm.Obj().Pkg().Path() == "sync" && a.p.sup.syncType["sync."+nm.Obj().Name()]
}

// interceptedSpawn: defer/go of a frontend-INTERCEPTED library member
// (slices.Sort, cmp.Compare) refuses by name (emit.go: "the direct call of
// this library member is frontend-intercepted … in expression-statement
// position only").
func (a *analyzer) interceptedSpawn(d *declReport, how string, call *ast.CallExpr, pos string) {
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return
	}
	if path, member, _, ok := a.stdlibSel(sel); ok && a.p.sup.intercept[path+"."+member] {
		d.add(finding{Cause: mustCause("intercepted-defer-go"), Key: how + " " + path + "." + member, Pos: pos, Certain: true})
	}
}

// boxes: assigning a component of static type src into a target of type
// dst is an implicit interface conversion (FR-7's shape) when dst is an
// interface and src is not identical to it.
func boxes(dst, src types.Type) bool {
	if dst == nil || src == nil {
		return false
	}
	// emit.go (FR-7 arms): `types.IsInterface(target) && !types.IsInterface(comp)`
	// — an interface-to-interface component is NOT refused.
	return types.IsInterface(dst) && !types.IsInterface(src)
}

// readsOuter: does expr contain a BARE identifier `name` resolving to an
// object other than newObj? Selector members (`r.trk`) and struct-literal
// field keys are not variable reads and are skipped.
func (a *analyzer) readsOuter(expr ast.Expr, name string, newObj types.Object) bool {
	found := false
	var walk func(n ast.Node) bool
	walk = func(n ast.Node) bool {
		if found || n == nil {
			return false
		}
		switch x := n.(type) {
		case *ast.SelectorExpr:
			ast.Inspect(x.X, walk)
			return false
		case *ast.KeyValueExpr:
			if _, isId := x.Key.(*ast.Ident); isId {
				ast.Inspect(x.Value, walk)
				return false
			}
		case *ast.Ident:
			if x.Name == name {
				if u := a.info.Uses[x]; u != nil && u != newObj {
					if _, isVar := u.(*types.Var); isVar {
						found = true
					}
				}
			}
		}
		return true
	}
	ast.Inspect(expr, walk)
	return found
}

// shortCircuit scans the RIGHT operand of && / || for the FR-2 / FR-18
// shapes (a receive; an allocation, tuple splat) without entering closures.
func (a *analyzer) shortCircuit(d *declReport, y ast.Expr) {
	ast.Inspect(y, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.FuncLit:
			return false
		case *ast.UnaryExpr:
			if x.Op == token.ARROW {
				d.add(finding{Cause: mustCause("recv-short-circuit"), Key: "<-ch in RHS", Pos: a.p.pos(x), Certain: true})
			}
			if x.Op == token.AND {
				if _, isLit := x.X.(*ast.CompositeLit); isLit {
					d.add(finding{Cause: mustCause("alloc-short-circuit"), Key: "&composite in RHS", Pos: a.p.pos(x), Certain: true})
				}
			}
		case *ast.CompositeLit:
			// emit.go: hoistSliceLit / emitMapLit refuse under hoistForbidden;
			// a struct or array VALUE literal is not hoisted and lowers.
			if tv, ok := a.info.Types[x]; ok && tv.Type != nil {
				switch tv.Type.Underlying().(type) {
				case *types.Slice:
					d.add(finding{Cause: mustCause("alloc-short-circuit"), Key: "slice literal in RHS", Pos: a.p.pos(x), Certain: true})
				case *types.Map:
					d.add(finding{Cause: mustCause("alloc-short-circuit"), Key: "map literal in RHS", Pos: a.p.pos(x), Certain: true})
				}
			}
		case *ast.CallExpr:
			if name, ok := isBuiltin(a, x.Fun); ok && (name == "make" || name == "new" || name == "append" || name == "copy") {
				d.add(finding{Cause: mustCause("alloc-short-circuit"), Key: name + " in RHS", Pos: a.p.pos(x), Certain: true})
			}
			if len(x.Args) == 1 {
				if tv, ok := a.info.Types[x.Args[0]]; ok {
					if tup, ok := tv.Type.(*types.Tuple); ok && tup.Len() > 1 {
						d.add(finding{Cause: mustCause("alloc-short-circuit"), Key: "tuple splat f(g()) in RHS", Pos: a.p.pos(x), Certain: true})
					}
				}
			}
		}
		return true
	})
}
