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

// The strings.Builder and bytes.Buffer shadow models (raft W4.1 item 2 /
// W4.3) were RETIRED in stdlib source-through slice 2 (2026-09-03, memo
// §3 rows T1/T2): both types lower from the pinned GOROOT text as
// members of the `strings` / `bytes` library units, Builder's three
// `unsafe` sites through the byte-checked overlay (stdlib-overlay.tsv).
// Their conformance rows (strings/builder-model/*, bytes/buffer-model/*,
// fmt/fprint-writers/*, fmt/fprintf-builder/*) now exercise the REAL
// bodies; Cap/Grow/WriteRune and the Buffer read side, stubs under the
// models, are real too (strings/builder-cap/* pins Cap under the R2
// append-spill envelope as membership rows).

// importedTypeModel describes one modeled imported type.
type importedTypeModel struct {
	pkgPath string
	pkgName string
	src     string
	// methods with REAL bodies in the model (unexported helpers
	// included); the type's other exported methods stay stubs.
	modeled map[string]bool
	// intrinsic: the model's package-level functions are BODYLESS
	// declarations lowered at their CALL sites by a dedicated emitter
	// arm (sync/atomic — atomics.go); `lowerShadowModel` drops the
	// declarations before emission, admitting the bodyless shape only
	// for names `atomicIntrinsicDecl` recognizes. Models without this
	// flag refuse any bodyless declaration (the standing rule).
	intrinsic bool
}

// modeledImportedTypes: qualified type name -> shadow model. Since slice
// 2 the only entries are the sync/atomic typed wrappers (atomics.go
// registers them at init — memory-model-owned intrinsics, not library
// text); the table stays the single place a shadow model can land, and
// the register (stdlibregister.go) counts it.
var modeledImportedTypes = map[string]*importedTypeModel{}

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
				// A def in the MODEL's package is the model's to
				// declare — including named FIELD types (bytes.readOp)
				// the host may have reached through the real package's
				// type info and emitted only as a D5 MARKER (whose
				// default value refuses). The merge site REPLACES any
				// same-named host def with this one.
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
	// The shadow models are checked at the same pinned language
	// version as subject code (langversion.go; unset would disable
	// version checking here too).
	lang, err := pinnedLangVersion()
	if err != nil {
		return nil, nil, err
	}
	conf := types.Config{Importer: nil, GoVersion: lang}
	pkg, err := conf.Check(model.pkgPath, fset, []*ast.File{file}, info)
	if err != nil {
		return nil, nil, fmt.Errorf("internal: imported-type model %s failed to type-check: %w", model.pkgPath, err)
	}
	// The model's INTRINSIC surface (atomics.go): bodyless package-level
	// declarations exist only for go/types to resolve the method
	// bodies' calls; they are dropped here — the emitter's atomic-call
	// arm lowers every call site — and any OTHER bodyless declaration
	// refuses (the general emitter would refuse it too, "bodyless
	// function", but naming the model here keeps the cause legible).
	emitFile := file
	if model.intrinsic {
		kept := make([]ast.Decl, 0, len(file.Decls))
		for _, decl := range file.Decls {
			if fd, isFunc := decl.(*ast.FuncDecl); isFunc && fd.Body == nil {
				if !atomicIntrinsicDecl(fd) {
					return nil, nil, unsup("imported-type model %s: bodyless declaration %s is not an admitted intrinsic (fail closed)", model.pkgPath, fd.Name.Name)
				}
				continue
			}
			kept = append(kept, decl)
		}
		copied := *file
		copied.Decls = kept
		emitFile = &copied
	} else {
		for _, decl := range file.Decls {
			if fd, isFunc := decl.(*ast.FuncDecl); isFunc && fd.Body == nil {
				return nil, nil, unsup("imported-type model %s: bodyless declaration %s (only intrinsic models admit the shape — fail closed)", model.pkgPath, fd.Name.Name)
			}
		}
	}
	shadow := &emitter{fset: fset, info: info, pkg: pkg}
	program, err := shadow.emitProgram([]*ast.File{emitFile})
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
