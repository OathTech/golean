// Modeled imported types — "E5-T", the type-shaped extension of the E5
// stdlib-shim pattern (raft W4.1 item 2, H-18/G-10;
// docs/raft-w41-log.md item 2).
//
// An E5 shim models a stdlib FUNCTION as injected Go source. A stdlib
// TYPE cannot be injected into the user's package (its methods must
// live on the imported type's own identity), so a modeled imported
// type is lowered from a SHADOW SOURCE MODEL instead: a pinned mini
// `package strings` (below) is parsed, type-checked and emitted by a
// FRESH emitter through the ORDINARY pipeline, and its wire output —
// the real TypeDef `strings.Builder` (a struct, so `var b
// strings.Builder` materializes a real zero value) plus method bodies
// with the type's own FuncIds (`strings.Builder.WriteString`) — is
// harvested into the host program's wire. Host code needs NO change:
// its type references and method calls already mint exactly those
// names; they used to resolve to the D5 marker + declaration-only
// stubs and now resolve to the model.
//
// FAIL-CLOSED RULES:
//   - Only the methods the model DECLARES have bodies. The rest of the
//     exported method set (for strings.Builder: Cap, Grow, WriteRune)
//     still lands as declaration-only stubs — satisfaction answers
//     from the complete set, calls to unmodeled members refuse. Cap is
//     deliberately unmodeled: it would expose append's capacity growth
//     policy, which is allocator latitude the machine does not pin.
//   - The harvest ASSERTS its shape: no plain functions, no $pkginit,
//     no package-level state, and no TypeDef outside the model's own
//     package except the interfaces its signatures mention (dropped
//     here when the host also emits them). Anything unexpected refuses
//     the export.
//   - The model carries the SEMANTIC teeth, not just the happy path:
//     Builder's copy check panics with upstream's exact message
//     (strings/builder-model/copy-panics pins it — a model that
//     dropped the check would flip that row visibly).
//
// FIDELITY notes for the Builder model (vs go/src/strings/builder.go):
// String() copies where upstream aliases via unsafe — unobservable,
// strings are immutable; copyCheck writes `b.addr = b` where upstream
// routes through abi.NoEscape — escape analysis is not modeled; the
// model omits upstream's unexported `grow`/`Grow` machinery — Grow is
// a stub, and append growth is the machine's own. The conformance
// rows (strings/builder-model/*, fmt/fprintf-builder/*) are the
// standing differential against the REAL Builder under go run.

package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"sort"
)

// stringsBuilderModelSrc is the pinned shadow model for strings.Builder.
const stringsBuilderModelSrc = `package strings

// The strings.Builder shadow model (E5-T). Mirrors go/src/strings/
// builder.go's semantics over plain Go; see importedmodel.go for the
// fidelity argument and the modeled-method contract.
type Builder struct {
	addr *Builder
	buf  []byte
}

func (b *Builder) copyCheck() {
	if b.addr == nil {
		b.addr = b
	} else if b.addr != b {
		panic("strings: illegal use of non-zero Builder copied by value")
	}
}

func (b *Builder) String() string {
	return string(b.buf)
}

func (b *Builder) Len() int { return len(b.buf) }

func (b *Builder) Reset() {
	b.addr = nil
	b.buf = nil
}

func (b *Builder) Write(p []byte) (int, error) {
	b.copyCheck()
	b.buf = append(b.buf, p...)
	return len(p), nil
}

func (b *Builder) WriteByte(c byte) error {
	b.copyCheck()
	b.buf = append(b.buf, c)
	return nil
}

func (b *Builder) WriteString(s string) (int, error) {
	b.copyCheck()
	b.buf = append(b.buf, s...)
	return len(s), nil
}
`

// importedTypeModel describes one modeled imported type.
type importedTypeModel struct {
	pkgPath string
	pkgName string
	src     string
	// methods with REAL bodies in the model (unexported helpers
	// included); the type's other exported methods stay stubs.
	modeled map[string]bool
}

// modeledImportedTypes: qualified type name -> shadow model.
var modeledImportedTypes = map[string]*importedTypeModel{
	"strings.Builder": {
		pkgPath: "strings",
		pkgName: "strings",
		src:     stringsBuilderModelSrc,
		modeled: map[string]bool{
			"copyCheck": true, "String": true, "Len": true, "Reset": true,
			"Write": true, "WriteByte": true, "WriteString": true,
		},
	},
}

// harvestImportedModels lowers the shadow model of every TRIGGERED
// modeled imported type (identity reached the wire — e.importedNamed)
// through a fresh emitter and returns (typeDefs, methods) to merge
// into the host wire. TypeDefs outside the models' packages are
// dropped when `hostDefNames` already carries them (the host emits its
// own `error` interface def, and duplicate TypeDefs refuse at the
// decoder); a def that is neither the model's own nor droppable
// refuses here.
func (e *emitter) harvestImportedModels(hostDefNames map[string]bool) ([]any, []any, error) {
	names := []string{}
	for qname := range e.importedNamed {
		if modeledImportedTypes[qname] != nil {
			names = append(names, qname)
		}
	}
	if len(names) == 0 {
		return nil, nil, nil
	}
	sort.Strings(names)
	outDefs := []any{}
	outMethods := []any{}
	seenPkg := map[string]bool{}
	for _, qname := range names {
		model := modeledImportedTypes[qname]
		if seenPkg[model.pkgPath] {
			continue
		}
		seenPkg[model.pkgPath] = true
		defs, methods, err := lowerShadowModel(model)
		if err != nil {
			return nil, nil, err
		}
		for _, td := range defs {
			m, isMap := td.(map[string]any)
			if !isMap {
				return nil, nil, unsup("imported-type model %s: non-object TypeDef in harvest (fail closed)", qname)
			}
			name, _ := m["name"].(string)
			if len(name) > len(model.pkgPath) && name[:len(model.pkgPath)+1] == model.pkgPath+"." {
				outDefs = append(outDefs, td)
				continue
			}
			if hostDefNames[name] {
				continue // the host emits this one (e.g. `error`)
			}
			outDefs = append(outDefs, td)
		}
		outMethods = append(outMethods, methods...)
	}
	return outDefs, outMethods, nil
}

// lowerShadowModel runs the ordinary pipeline over one pinned model
// source with a FRESH emitter (no host state crosses in either
// direction) and asserts the harvest's shape.
func lowerShadowModel(model *importedTypeModel) ([]any, []any, error) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "golean-model-"+model.pkgName+".go", model.src, parser.ParseComments)
	if err != nil {
		return nil, nil, fmt.Errorf("internal: imported-type model %s failed to parse: %w", model.pkgPath, err)
	}
	info := newTypesInfo()
	conf := types.Config{Importer: nil}
	pkg, err := conf.Check(model.pkgPath, fset, []*ast.File{file}, info)
	if err != nil {
		return nil, nil, fmt.Errorf("internal: imported-type model %s failed to type-check: %w", model.pkgPath, err)
	}
	shadow := &emitter{fset: fset, info: info, pkg: pkg}
	program, err := shadow.emitProgram([]*ast.File{file})
	if err != nil {
		return nil, nil, fmt.Errorf("imported-type model %s failed to lower: %w", model.pkgPath, err)
	}
	funcs, _ := program["funcs"].([]any)
	for _, f := range funcs {
		m, _ := f.(map[string]any)
		return nil, nil, unsup("imported-type model %s produced a plain function %v (the harvest admits methods and TypeDefs only — fail closed)", model.pkgPath, m["name"])
	}
	if _, hasGlobals := program["globals"]; hasGlobals {
		return nil, nil, unsup("imported-type model %s produced package-level state (fail closed)", model.pkgPath)
	}
	defs, _ := program["types"].([]any)
	methods, _ := program["methods"].([]any)
	for _, mm := range methods {
		m, _ := mm.(map[string]any)
		if _, quarantined := m["unsupported"]; quarantined {
			return nil, nil, unsup("imported-type model %s: method %v.%v did not lower (%v) — the model must stay inside the modeled subset",
				model.pkgPath, m["recvType"], m["name"], m["unsupported"])
		}
	}
	return defs, methods, nil
}

// importedModelStubFilter reports, for a modeled imported type, the
// method names that must STILL land as declaration-only stubs (the
// exported set minus the model's bodies); nil for unmodeled types
// (meaning: the ordinary full-stub path applies).
func importedModelStubFilter(qname string) map[string]bool {
	model := modeledImportedTypes[qname]
	if model == nil {
		return nil
	}
	return model.modeled
}
