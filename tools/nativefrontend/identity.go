package main

// identity.go — the multi-package identity boundary (raft W1.1,
// docs/2026-08-18_multipackage-identity.md). Wire TypeId/FuncId/global
// qualifiers are minted HERE (and in qualifiedTypeName, which shares
// pkgQualifier): import-path-qualified, main-package names bare —
// grammar injectivity per the design note §1. GoCore sees only the
// resulting opaque strings.

import (
	"go/ast"
	"go/types"
	"sort"
	"strconv"
	"strings"
)

// setUnits installs the loaded source units (program initialization
// order, main LAST) and derives the membership views.
func (e *emitter) setUnits(units []*sourcePkg) {
	e.units = units
	e.srcPkgSet = map[*types.Package]*sourcePkg{}
	for _, u := range units {
		e.srcPkgSet[u.pkg] = u
	}
	e.mainPkg = units[len(units)-1].pkg
}

// setUnit switches the emitter's per-package state to the unit whose
// declarations are being emitted. e.pkg feeds go/types visibility
// (LookupFieldOrMethod) and the scope checks; e.info is the unit's own
// type-checker record (Uses/Defs/Types/Selections/Instances/InitOrder
// are AST-node-keyed, and the nodes belong to exactly one unit).
func (e *emitter) setUnit(u *sourcePkg) {
	e.pkg = u.pkg
	e.info = u.info
	e.curUnit = u
}

// isLibraryPackage: the package is a stdlib source-through LIBRARY unit
// (stdlibsource.go) — a source package (isSourcePackage is true of it
// too) whose declarations are emitted reachability-pruned and whose
// calls never route through the user-package shims.
func (e *emitter) isLibraryPackage(pkg *types.Package) bool {
	if pkg == nil || e.units == nil {
		return false
	}
	u := e.srcPkgSet[pkg]
	return u != nil && u.library
}

// isSourcePackage: the package is part of the program under lowering
// (main or a case-local import) — as opposed to stdlib. Nil-units
// fallback: the single directly-constructed package.
func (e *emitter) isSourcePackage(pkg *types.Package) bool {
	if pkg == nil {
		return false
	}
	if e.units == nil {
		return pkg == e.pkg
	}
	return e.srcPkgSet[pkg] != nil
}

// isMainPackage: the subject namespace (bare FuncIds).
func (e *emitter) isMainPackage(pkg *types.Package) bool {
	if e.units == nil {
		return pkg == e.pkg
	}
	return pkg == e.mainPkg
}

// isSourceScope reports whether a variable's parent scope is some
// source package's scope — the package-level-variable classification
// (globals resolve to driver-seeded cells, never captures).
func (e *emitter) isSourceScope(parent *types.Scope) bool {
	if parent == nil {
		return false
	}
	if e.units == nil {
		return parent == e.pkg.Scope()
	}
	for _, u := range e.units {
		if parent == u.pkg.Scope() {
			return true
		}
	}
	return false
}

// pkgQualifier returns the wire qualifier for a declaring package: its
// IMPORT PATH (Go's identity — the BUG-010 fix). A path the key grammar
// or gc's link-symbol spelling cannot carry verbatim (keyPathHazard) is
// RECORDED here for checkKeyPathGrammar's fail-closed refusal.
func (e *emitter) pkgQualifier(pkg *types.Package) string {
	p := pkg.Path()
	if why := keyPathHazard(p); why != "" {
		if e.badKeyPaths == nil {
			e.badKeyPaths = map[string]string{}
		}
		e.badKeyPaths[p] = why
	}
	return p
}

// keyPathHazard names why an import path cannot be a wire qualifier, or
// returns "" when it can. Three classes, each a byte-exactness hazard:
//   - '.' — the key grammar's qualifier/name separator (identity note
//     §3.2; `TypeId.unqualified` strips at the FIRST '.').
//   - '·' U+00B7 — the scope-ordinal marker of function-local TypeIds
//     (design note 2026-09-05 §2.1): legal in an import path by
//     spec#Import_declarations (category Po), never in an identifier.
//   - every byte gc's `objabi.PathToPrefix` %-escapes in a link symbol —
//     bytes >= 0x7F, '%', '"', space and control characters (audit fix
//     round R11, 2026-09-05 [AGENT]): an instantiation bracket is gc's
//     LinkString, so `Pair[pkgs/naïve.T]` DISPLAYS as
//     `main.Pair[pkgs/na%c3%afve.T]` while the key (= the display's
//     bracket, mono.go) spells the raw path; no display record could be
//     byte-exact, and only the abort renderer's non-ASCII refusal masked
//     it. Refused at the minting boundary instead of modeled: a path
//     with such bytes is legal Go (category L letters), so this is a
//     named coverage refusal, not a wrong answer.
func keyPathHazard(p string) string {
	if strings.Contains(p, ".") {
		return "contains '.' (the key grammar's qualifier/name separator)"
	}
	if strings.Contains(p, "·") {
		return "contains '·' U+00B7 (the local-type scope-ordinal marker)"
	}
	for i := 0; i < len(p); i++ {
		c := p[i]
		if c >= 0x7F || c <= ' ' || c == '%' || c == '"' {
			return "contains a byte gc's objabi.PathToPrefix %-escapes (>= 0x7F, '%', '\"', space/control), so gc's LinkString bracket would display the escaped path where the key spells the raw one"
		}
	}
	return ""
}

// funcWireName mints the wire FuncId of a PACKAGE-LEVEL function
// (methods key by receiver TypeId instead — never routed here):
// main-package and universe names stay BARE (the subject namespace;
// dot-free, so they cannot collide with qualified keys), source
// packages qualify by import path. NON-source (stdlib) functions stay
// bare too: no static-call path exists for them except shims/externs,
// and the recorded stdlib dot-import defect (stdlibshim.go FAIL-CLOSED
// RULES) keeps its exact shape — neither fixed nor widened here.
func (e *emitter) funcWireName(fn *types.Func) string {
	pkg := fn.Pkg()
	if pkg == nil || e.isMainPackage(pkg) || !e.isSourcePackage(pkg) {
		return fn.Name()
	}
	return e.pkgQualifier(pkg) + "." + fn.Name()
}

// globalWireName mints the wire NAME of a package-level variable (the
// gid stays the identity; the name feeds the decoder's duplicate
// refusal and human-readable wires).
func (e *emitter) globalWireName(v *types.Var) string {
	pkg := v.Pkg()
	if pkg == nil || e.isMainPackage(pkg) || !e.isSourcePackage(pkg) {
		return v.Name()
	}
	return e.pkgQualifier(pkg) + "." + v.Name()
}

// initFuncWireName mints the reserved id of the unit's n-th init()
// function: `$initN` for main (unchanged), `<path>.$initN` otherwise.
func (e *emitter) initFuncWireName(u *sourcePkg, n int) string {
	name := "$init" + itoa(n)
	if u.pkg == e.mainPkg {
		return name
	}
	return e.pkgQualifier(u.pkg) + "." + name
}

// checkKeyPathGrammar fails the export when an import path the key
// grammar cannot carry (keyPathHazard) reached a wire qualifier:
// `TypeId.unqualified` (the reflect-Name observation contract) strips at
// the FIRST '.', the key injectivity argument (identity note §1) needs
// dot-free qualifiers, and gc's link-symbol escaping makes a display
// over a non-ASCII path unreproducible. Fail closed at the boundary that
// minted the key, like the package-name collision check this replaces;
// every offending path is named with its reason.
func (e *emitter) checkKeyPathGrammar() error {
	if len(e.badKeyPaths) == 0 {
		return nil
	}
	paths := make([]string, 0, len(e.badKeyPaths))
	for p := range e.badKeyPaths {
		paths = append(paths, p)
	}
	sort.Strings(paths)
	named := make([]string, len(paths))
	for i, p := range paths {
		named[i] = strconv.Quote(p) + " " + e.badKeyPaths[p]
	}
	return unsup("import path(s) unusable as wire identity qualifiers: %s — the key grammar reserves '.' for the qualifier/name separator and '·' for the local-type scope ordinal, and gc's objabi.PathToPrefix %%-escapes bytes >= 0x7F / '%%' / '\"' / space in the LinkString brackets a display reproduces (docs/2026-08-18_multipackage-identity.md §3; docs/2026-09-05_fr19-bug097-design.md §2.1); vendor at a dot-free ASCII path", strings.Join(named, "; "))
}

// ---- identity vs display (docs/2026-09-05_fr19-bug097-design.md §0) ----
//
// A TypeId's KEY is its identity: path-qualified, scope-disambiguated
// for function-local types, structural for anonymous interfaces — the
// machine decides by it and by nothing else. Its DISPLAY is gc's runtime
// type string (`NameString`, cmd/compile/internal/types/fmt.go
// fmtTypeIDName @ go1.26.5): package-NAME qualified, no scope
// information, deliberately ambiguous — the machine renders panic texts
// from it and decides nothing by it. Every key minted by a boundary
// constructor (qualifiedTypeName, instTypeId, anonIfaceKey, the
// synthetic markers) registers its display here; emitProgram attaches
// `display`/`pkg` to every TypeDef and refuses a key with no record.

// typeDisplay is the wire's display record of one TypeId.
type typeDisplay struct {
	display string // gc's NameString of the type
	pkg     string // declaring import path; "" for unnamed, universe and synthetic types
}

// noteTypeDisplay records the display of a minted key. Display is a
// FUNCTION of the key (the key is injective over identity, the display
// is a function of identity), so a second registration must agree; a
// disagreement is a minting defect, recorded for the fail-closed
// refusal in emitProgram (displayConflictRefusal).
func (e *emitter) noteTypeDisplay(key string, d typeDisplay) {
	if e.typeDisplays == nil {
		e.typeDisplays = map[string]typeDisplay{}
	}
	if prev, ok := e.typeDisplays[key]; ok {
		if prev != d {
			e.displayConflicts = append(e.displayConflicts,
				key+" ("+prev.display+"/"+prev.pkg+" vs "+d.display+"/"+d.pkg+")")
		}
		return
	}
	e.typeDisplays[key] = d
}

// displayConflictRefusal refuses the export when one key was registered
// with two displays (see noteTypeDisplay). Deduplicated and sorted, so
// the text is deterministic.
func (e *emitter) displayConflictRefusal() error {
	if len(e.displayConflicts) == 0 {
		return nil
	}
	seen := map[string]bool{}
	uniq := []string{}
	for _, c := range e.displayConflicts {
		if !seen[c] {
			seen[c] = true
			uniq = append(uniq, c)
		}
	}
	sort.Strings(uniq)
	return unsup("TypeId registered with two different display records: %s", strings.Join(uniq, "; "))
}

// attachTypeDisplays writes `display`/`pkg` onto every TypeDef entry
// from the registry. A TypeDef whose key has no record was minted
// outside the boundary constructors — refuse by name.
func (e *emitter) attachTypeDisplays(typeDefs []any) error {
	if err := e.displayConflictRefusal(); err != nil {
		return err
	}
	for _, td := range typeDefs {
		m, ok := td.(map[string]any)
		if !ok {
			return unsup("TypeDef entry of unexpected shape %T", td)
		}
		name, _ := m["name"].(string)
		// A TypeDef harvested from a shadow model's own FRESH emitter
		// (importedmodel.go lowerShadowModel → emitProgram) already
		// carries the record that emitter attached; register it here so
		// a host-side disagreement is caught like any other.
		if disp, hasD := m["display"].(string); hasD {
			if pkg, hasP := m["pkg"].(string); hasP {
				e.noteTypeDisplay(name, typeDisplay{display: disp, pkg: pkg})
			}
		}
		d, ok := e.typeDisplays[name]
		if !ok {
			return unsup("TypeDef %s has no display record — its key was minted outside the identity boundary constructors (docs/2026-09-05_fr19-bug097-design.md §3.1)", name)
		}
		m["display"] = d.display
		m["pkg"] = d.pkg
	}
	return nil
}

// localTypeOrdinal returns the scope ordinal of a FUNCTION-LOCAL type
// declaration (design note §2.2): its 1-based index among every local
// `type` declaration of its package, in source order — files in the
// loader's order (lexical filename order), positions ascending. Built
// once per package from types.Info.Defs. A local TypeName the table does
// not know cannot be keyed: recorded in badLocalTypes for the
// fail-closed refusal (checkLocalTypeOrdinals), never a bare key.
func (e *emitter) localTypeOrdinal(obj *types.TypeName) (int, bool) {
	if e.localOrdinals == nil {
		e.localOrdinals = map[*types.TypeName]int{}
		if e.units == nil {
			if e.info != nil && e.pkg != nil {
				e.indexLocalTypes(e.pkg, e.info, nil)
			}
		} else {
			for _, u := range e.units {
				e.indexLocalTypes(u.pkg, u.info, u.files)
			}
		}
	}
	n, ok := e.localOrdinals[obj]
	if !ok {
		if e.badLocalTypes == nil {
			e.badLocalTypes = map[string]bool{}
		}
		e.badLocalTypes[obj.Pkg().Path()+"."+obj.Name()] = true
	}
	return n, ok
}

// indexLocalTypes assigns one package's local-type ordinals.
func (e *emitter) indexLocalTypes(pkg *types.Package, info *types.Info, files []*ast.File) {
	type entry struct {
		obj  *types.TypeName
		file int
		pos  int
	}
	fileOf := func(pos int) int {
		for i, f := range files {
			if int(f.FileStart) <= pos && pos < int(f.FileEnd) {
				return i
			}
		}
		return len(files)
	}
	entries := []entry{}
	for _, obj := range info.Defs {
		tn, ok := obj.(*types.TypeName)
		if !ok || tn.Pkg() != pkg || tn.Parent() == pkg.Scope() || tn.IsAlias() {
			continue
		}
		// Type PARAMETERS are TypeNames in a non-package scope too; they
		// never mint TypeIds (substituted before any key is rendered).
		if _, isTP := tn.Type().(*types.TypeParam); isTP {
			continue
		}
		entries = append(entries, entry{tn, fileOf(int(tn.Pos())), int(tn.Pos())})
	}
	sort.Slice(entries, func(i, j int) bool {
		if entries[i].file != entries[j].file {
			return entries[i].file < entries[j].file
		}
		return entries[i].pos < entries[j].pos
	})
	for i, en := range entries {
		e.localOrdinals[en.obj] = i + 1
	}
}

// declaredInActiveStencil reports whether a (function-local) type is
// declared INSIDE the generic declaration currently being stenciled —
// the BUG-018 shape whose key and display carry the instantiation's
// type arguments. A local type the stencil merely mentions (its own
// type argument, a caller's local type reaching it through the
// substitution) is declared elsewhere and keeps its own key.
func (e *emitter) declaredInActiveStencil(obj *types.TypeName) bool {
	d := e.curInstDecl
	if d == nil || e.curTargs == nil {
		return false
	}
	return d.Pos() <= obj.Pos() && obj.Pos() < d.End()
}

// ---- unexported interface methods across packages (BUG-098) ----
//
// spec#Type_identity / spec#Uniqueness_of_identifiers: an unexported
// method name is qualified by its package — `red/inner.get` and
// `blue/inner.get` are different names, so red's `T` (method `get`)
// does NOT implement blue's `interface{ get() int }` (gc probe P5:
// `true false`). The wire's requirement lists (MethodSig.name), method
// tables (MethodInfo.name) and dispatch anchors carry BARE names, so the
// machine would judge it satisfied — a wrong answer. Until the names are
// package-qualified on the wire (the BUG-098 plan), the export REFUSES
// whenever an unexported requirement declared in package P shares its
// name with a concrete method declared in a different source package Q:
// the only shape on which the bare-name tables can answer wrong. Single-
// package programs never trip it (P == Q).

// noteUnexportedRequirements records the declaring package of every
// unexported method an interface reaching the wire requires.
func (e *emitter) noteUnexportedRequirements(iface *types.Interface) {
	for i := 0; i < iface.NumMethods(); i++ {
		m := iface.Method(i)
		if m.Exported() || m.Pkg() == nil {
			continue
		}
		if e.unexportedReqs == nil {
			e.unexportedReqs = map[string]map[string]bool{}
		}
		if e.unexportedReqs[m.Name()] == nil {
			e.unexportedReqs[m.Name()] = map[string]bool{}
		}
		e.unexportedReqs[m.Name()][m.Pkg().Path()] = true
	}
}

// checkUnexportedMethodScopes refuses the export on the BUG-098 hazard
// shape (see above): an unexported requirement name declared in package
// P for which some OTHER source package Q declares a concrete method of
// that name.
func (e *emitter) checkUnexportedMethodScopes() error {
	if len(e.unexportedReqs) == 0 {
		return nil
	}
	concrete := map[string]map[string]bool{}
	record := func(pkg *types.Package, info *types.Info) {
		for _, obj := range info.Defs {
			fn, ok := obj.(*types.Func)
			if !ok || fn.Exported() || fn.Pkg() != pkg {
				continue
			}
			sig, ok := fn.Type().(*types.Signature)
			if !ok || sig.Recv() == nil {
				continue
			}
			// Interface methods are requirements, not concrete methods.
			if _, isIface := types.Unalias(sig.Recv().Type()).Underlying().(*types.Interface); isIface {
				continue
			}
			if concrete[fn.Name()] == nil {
				concrete[fn.Name()] = map[string]bool{}
			}
			concrete[fn.Name()][pkg.Path()] = true
		}
	}
	if e.units == nil {
		if e.pkg != nil && e.info != nil {
			record(e.pkg, e.info)
		}
	} else {
		for _, u := range e.units {
			record(u.pkg, u.info)
		}
	}
	hazards := []string{}
	for name, reqPkgs := range e.unexportedReqs {
		for req := range reqPkgs {
			for impl := range concrete[name] {
				if impl != req {
					hazards = append(hazards, name+" (required by "+req+", implemented in "+impl+")")
				}
			}
		}
	}
	if len(hazards) == 0 {
		return nil
	}
	sort.Strings(hazards)
	return unsup("unexported interface method name(s) shared across packages: %s — an unexported method name is package-scoped (spec#Type_identity) but the wire's method tables carry bare names, so satisfaction could answer wrong; refused (BUG-098, docs/2026-09-05_fr19-bug097-design.md §2.5)", strings.Join(hazards, "; "))
}

// checkLocalTypeOrdinals fails the export when a function-local type
// reached a key without an ordinal.
func (e *emitter) checkLocalTypeOrdinals() error {
	if len(e.badLocalTypes) == 0 {
		return nil
	}
	names := []string{}
	for n := range e.badLocalTypes {
		names = append(names, n)
	}
	sort.Strings(names)
	return unsup("function-local type(s) %v reached a TypeId without a scope ordinal (not among the loaded units' declarations — docs/2026-09-05_fr19-bug097-design.md §2.2)", names)
}

// gcSortedMethods returns an interface's FULL method set (embedded
// interfaces flattened by go/types) in gc's order — types.CompareSyms
// (cmd/compile/internal/types/sym.go): exported names first, by name;
// then unexported names by name, then by declaring package path. Both
// the identity key and the display use it, so one method set has one
// spelling.
func gcSortedMethods(iface *types.Interface) []*types.Func {
	ms := make([]*types.Func, iface.NumMethods())
	for i := range ms {
		ms[i] = iface.Method(i)
	}
	sort.SliceStable(ms, func(i, j int) bool {
		a, b := ms[i], ms[j]
		ea, eb := a.Exported(), b.Exported()
		if ea != eb {
			return ea
		}
		if a.Name() != b.Name() {
			return a.Name() < b.Name()
		}
		if ea {
			return false
		}
		return pkgPathOf(a.Pkg()) < pkgPathOf(b.Pkg())
	})
	return ms
}

func pkgPathOf(p *types.Package) string {
	if p == nil {
		return ""
	}
	return p.Path()
}

// anonIfaceKey mints the identity KEY of an anonymous non-empty
// interface (design note §2.1/§2.3): `interface{` + methods in gc's
// order, `;`-joined, `}`; an unexported method name is qualified by its
// declaring package PATH (spec#Type_identity: unexported method names
// from different packages are different — go/types' TypeString never
// qualifies them, probe P3), parameter/result types render through
// renderTypeKey in ifaceKeyCtx (declared types by path, function-local
// types by scope ordinal, nested anonymous interfaces recursively).
// Registers the display alongside. Substitution-aware: callers pass the
// interface at the active instantiation (emitType applies applySubst;
// noteInterface substitutes again, idempotently).
func (e *emitter) anonIfaceKey(iface *types.Interface) (string, error) {
	if iface.Empty() {
		return emptyInterfaceName, nil
	}
	if !iface.IsMethodSet() {
		return "", unsup("non-method-set interface type %s (type constraints are not interface values)", iface)
	}
	parts := []string{}
	for _, m := range gcSortedMethods(iface) {
		name := m.Name()
		if !m.Exported() {
			if m.Pkg() == nil {
				return "", unsup("unexported interface method %s with no declaring package", name)
			}
			name = e.pkgQualifier(m.Pkg()) + "." + name
		}
		sig, err := e.renderSignatureKey(m.Type().(*types.Signature), ifaceKeyCtx, false)
		if err != nil {
			return "", err
		}
		parts = append(parts, name+sig)
	}
	key := "interface{" + strings.Join(parts, ";") + "}"
	disp, err := e.gcTypeString(iface)
	if err != nil {
		return "", err
	}
	// pkg is "" BY gc's RULE, not by omission (audit fix round R1,
	// 2026-09-05 [AGENT]): reflectdata/reflect.go's TINTER arm sets the
	// interfacetype's PkgPath only for a NAMED interface (`t.Sym() != nil`,
	// excluding the `error` universe type); an anonymous interface has no
	// Sym, so `rtype.pkgpath()` of it is "" whatever its unexported
	// methods' packages are — those travel per method name (`dname(...,
	// pkg, ...)` when `a.name.Pkg != tpkg`), not on the type.
	e.noteTypeDisplay(key, typeDisplay{display: disp, pkg: ""})
	return key, nil
}

// gcTypeString renders a type exactly as gc's runtime type string does —
// cmd/compile/internal/types/fmt.go tconv2 in fmtTypeIDName mode, the
// string reflectdata.dcommontype stores (reflect.Type.String(), `%T`,
// every `interface conversion:` panic) — verified line by line against
// the go1.26.5 probes in docs/evidence/2026-09-05_fr19-bug097/gc-probes.txt.
// DISPLAY ONLY: never a key, never compared. Named types render by
// PACKAGE NAME with no scope information (gc trims the `·N` vargen
// suffix); an instantiation's bracket is gc's LinkString of the
// arguments, which on the admitted mangling surface is exactly
// renderTypeArg's spelling. Refuses (rather than guesses) on a type
// parameter outside an instantiation, a tuple, or anything renderTypeArg
// refuses inside a bracket (C6 included: a local type's LinkString
// carries gc's compiler counter).
func (e *emitter) gcTypeString(t types.Type) (string, error) {
	if e.curSubst != nil {
		t = e.applySubst(t)
	}
	switch ty := t.(type) {
	case *types.Basic:
		if ty.Kind() == types.UnsafePointer {
			return "unsafe.Pointer", nil
		}
		if ty.Kind() == types.Invalid && e.substErr != nil {
			return "", e.substErr
		}
		return renderBasicArg(ty)
	case *types.Alias:
		return e.gcTypeString(types.Unalias(ty))
	case *types.TypeParam:
		return "", unsup("type parameter %s outside an instantiation (display)", ty)
	case *types.Named:
		obj := ty.Obj()
		if obj.Pkg() == nil {
			// Universe: only `error` is a value type here.
			return obj.Name(), nil
		}
		disp := obj.Pkg().Name() + "." + obj.Name()
		if ty.TypeArgs().Len() > 0 {
			args, err := e.renderTypeArgList(ty.TypeArgs())
			if err != nil {
				return "", err
			}
			return disp + "[" + args + "]", nil
		}
		// A type declared inside a generic function is named with the
		// enclosing instantiation's arguments (BUG-018; probe P4
		// `main.inner[int]`).
		if obj.Parent() != obj.Pkg().Scope() && e.declaredInActiveStencil(obj) {
			rendered := make([]string, len(e.curTargs))
			for i, ta := range e.curTargs {
				r, err := e.renderTypeArg(ta)
				if err != nil {
					return "", err
				}
				rendered[i] = r
			}
			disp += "[" + strings.Join(rendered, ",") + "]"
		}
		return disp, nil
	case *types.Pointer:
		elem, err := e.gcTypeString(ty.Elem())
		if err != nil {
			return "", err
		}
		return "*" + elem, nil
	case *types.Slice:
		elem, err := e.gcTypeString(ty.Elem())
		if err != nil {
			return "", err
		}
		return "[]" + elem, nil
	case *types.Array:
		elem, err := e.gcTypeString(ty.Elem())
		if err != nil {
			return "", err
		}
		return "[" + itoa64(ty.Len()) + "]" + elem, nil
	case *types.Map:
		k, err := e.gcTypeString(ty.Key())
		if err != nil {
			return "", err
		}
		v, err := e.gcTypeString(ty.Elem())
		if err != nil {
			return "", err
		}
		return "map[" + k + "]" + v, nil
	case *types.Chan:
		elem, err := e.gcTypeString(ty.Elem())
		if err != nil {
			return "", err
		}
		return chanSpelling(ty, elem), nil
	case *types.Signature:
		return e.gcSignatureString(ty, true)
	case *types.Interface:
		if ty.Empty() {
			return "interface {}", nil
		}
		parts := []string{}
		for _, m := range gcSortedMethods(ty) {
			name := m.Name()
			if !m.Exported() {
				if m.Pkg() == nil {
					return "", unsup("unexported interface method %s with no declaring package", name)
				}
				name = m.Pkg().Name() + "." + name
			}
			sig, err := e.gcSignatureString(m.Type().(*types.Signature), false)
			if err != nil {
				return "", err
			}
			parts = append(parts, name+sig)
		}
		return "interface { " + strings.Join(parts, "; ") + " }", nil
	case *types.Struct:
		if ty.NumFields() == 0 {
			return "struct {}", nil
		}
		parts := []string{}
		for i := 0; i < ty.NumFields(); i++ {
			f := ty.Field(i)
			ft, err := e.gcTypeString(f.Type())
			if err != nil {
				return "", err
			}
			part := ft
			if !f.Embedded() {
				// Field names print UNqualified in fmtTypeIDName
				// (fldconv: `verb == 'L'` and mode == fmtTypeIDName).
				part = f.Name() + " " + ft
			}
			if tag := ty.Tag(i); tag != "" {
				part += " " + strconv.Quote(tag)
			}
			parts = append(parts, part)
		}
		return "struct { " + strings.Join(parts, "; ") + " }", nil
	case *types.Tuple:
		return "", unsup("multi-value expression has no type string")
	default:
		return "", unsup("type %T (%s) has no gc display rendering", t, t)
	}
}

// gcSignatureString renders a signature in gc's spelling: parameters
// `(T, U)` (", "-joined, the variadic last as `...E`), results (none / ` R` /
// ` (R, S)`; `func` prefixed for a function TYPE, bare for an interface
// method (tconv2's TFUNC arm with verb 'S').
func (e *emitter) gcSignatureString(sig *types.Signature, withFunc bool) (string, error) {
	params := make([]string, sig.Params().Len())
	for i := range params {
		pt := sig.Params().At(i).Type()
		if sig.Variadic() && i == len(params)-1 {
			sl, ok := types.Unalias(e.applySubst(pt)).(*types.Slice)
			if !ok {
				return "", unsup("variadic parameter of non-slice type %s", pt)
			}
			el, err := e.gcTypeString(sl.Elem())
			if err != nil {
				return "", err
			}
			params[i] = "..." + el
			continue
		}
		p, err := e.gcTypeString(pt)
		if err != nil {
			return "", err
		}
		params[i] = p
	}
	out := "(" + strings.Join(params, ", ") + ")"
	if withFunc {
		out = "func" + out
	}
	switch sig.Results().Len() {
	case 0:
		return out, nil
	case 1:
		r, err := e.gcTypeString(sig.Results().At(0).Type())
		if err != nil {
			return "", err
		}
		return out + " " + r, nil
	default:
		rs := make([]string, sig.Results().Len())
		for i := range rs {
			r, err := e.gcTypeString(sig.Results().At(i).Type())
			if err != nil {
				return "", err
			}
			rs[i] = r
		}
		return out + " (" + strings.Join(rs, ", ") + ")", nil
	}
}

// chanSpelling is gc's channel spelling (tconv2 TCHAN): `chan T`,
// `chan<- T`, `<-chan T`, with `chan (<-chan T)` when the element is
// itself an unnamed receive-only channel.
func chanSpelling(ch *types.Chan, elem string) string {
	switch ch.Dir() {
	case types.RecvOnly:
		return "<-chan " + elem
	case types.SendOnly:
		return "chan<- " + elem
	}
	if inner, ok := ch.Elem().(*types.Chan); ok && inner.Dir() == types.RecvOnly {
		return "chan (" + elem + ")"
	}
	return "chan " + elem
}
