package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/printer"
	"go/token"
	"os"
	"path"
	"path/filepath"
	"strconv"
	"strings"
)

type config struct {
	input   string
	out     string
	subject string
	args    string
	status  string
	// splitStderr: the second mode (stdlib slice 3) — read a captured
	// oracle stderr and print the program's OWN output prefix as a JSON
	// string literal (split.go), exit 3 with the cause on any ambiguity.
	splitStderr string
}

func main() {
	var cfg config
	flag.StringVar(&cfg.input, "input", "", "input Go source")
	flag.StringVar(&cfg.out, "out", "", "output directory")
	flag.StringVar(&cfg.subject, "subject", "", "subject function")
	flag.StringVar(&cfg.args, "args", "-", "comma-separated integer args or -")
	flag.StringVar(&cfg.status, "expected-status", "ok", "expected Go status: ok, panic, deadlock, race, or fatal")
	flag.StringVar(&cfg.splitStderr, "split-stderr", "", "SPLIT MODE: path of a captured `go run` stderr; prints the program's output prefix for --expected-status as a JSON string literal (stdlib slice 3)")
	flag.Parse()

	if cfg.splitStderr != "" {
		raw, err := os.ReadFile(cfg.splitStderr)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		prefix, err := splitStderr(raw, cfg.status)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(3)
		}
		lit, err := outputLiteral(prefix)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		fmt.Print(lit)
		return
	}

	if err := run(cfg); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
}

func run(cfg config) error {
	if cfg.input == "" || cfg.out == "" || cfg.subject == "" {
		return fmt.Errorf("--input, --out, and --subject are required")
	}
	argValues, err := parseArgs(cfg.args)
	if err != nil {
		return err
	}

	// "deadlock" (channels arc slice 1): the subject blocks every goroutine
	// and the runtime detector aborts the run — like "panic", the subject
	// never returns, so no observable result is required. Deadlock cases
	// must never be built with -race (the detector does not fire there).
	// "race" (channels arc slice 3): the harness is built with -race by
	// the caller; the subject completes (the default GORACE continues
	// past a report), so the wrapper is the plain "ok" shape — the race
	// report and exit 66 arrive from the TSan runtime, not the wrapper.
	// "fatal" (spec-parity slice 2): the subject hits an unrecoverable
	// runtime throw (`fatal error: <msg>`, exit 2 — the sync misuse
	// class) — like deadlock, the subject never returns and no
	// observable result is required.
	if cfg.status != "ok" && cfg.status != "panic" && cfg.status != "deadlock" && cfg.status != "race" && cfg.status != "fatal" {
		return fmt.Errorf("invalid --expected-status %q", cfg.status)
	}

	inputDir := filepath.Dir(cfg.input)
	inputFiles, err := packageFiles(inputDir)
	if err != nil {
		return err
	}

	fset := token.NewFileSet()
	var subject *ast.FuncDecl
	parsed := []parsedFile{}
	for _, inputFile := range inputFiles {
		file, err := parser.ParseFile(fset, inputFile, nil, parser.ParseComments)
		if err != nil {
			return err
		}

		decls := file.Decls[:0]
		for _, decl := range file.Decls {
			fn, ok := decl.(*ast.FuncDecl)
			if ok && fn.Recv == nil && fn.Name.Name == "main" {
				continue
			}
			if ok && fn.Recv == nil && fn.Name.Name == cfg.subject {
				if subject != nil {
					return fmt.Errorf("duplicate subject function %q in package %s", cfg.subject, inputDir)
				}
				subject = fn
			}
			decls = append(decls, decl)
		}
		file.Decls = decls
		pruneUnusedImports(file)
		parsed = append(parsed, parsedFile{path: inputFile, file: file})
	}
	if subject == nil {
		return fmt.Errorf("subject function %q not found in %s", cfg.subject, inputDir)
	}

	harness, err := harnessSource(fset, subject, cfg.subject, argValues, cfg.status)
	if err != nil {
		return err
	}

	if err := os.RemoveAll(cfg.out); err != nil {
		return err
	}
	if err := os.MkdirAll(cfg.out, 0o755); err != nil {
		return err
	}
	for _, parsedFile := range parsed {
		source, err := formatNode(fset, parsedFile.file)
		if err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(cfg.out, filepath.Base(parsedFile.path)), source, 0o644); err != nil {
			return err
		}
	}
	// Multi-package cases (raft W1.1, identity note §7): copy every
	// case-local package the main package transitively imports into
	// <out>/gopath/src/<import path>, verbatim. The runner sets
	// GOPATH=<out>/gopath so `go run .` — Go's own resolution, the
	// oracle-side authority — resolves them; the harness invents no
	// resolution of its own (an unresolvable import stays a loud go-run
	// compile error).
	if err := copyLocalPackages(fset, inputDir, cfg.out); err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(cfg.out, "zz_golean_harness.go"), harness, 0o644)
}

// copyLocalPackages walks the main package's imports transitively: an
// import path P is case-local exactly when <inputDir>/P holds non-test
// .go files (import-DRIVEN — unimported subdirs, e.g. nested corpus
// cases, stay inert). Each local package's non-test files copy
// verbatim into <out>/gopath/src/P.
func copyLocalPackages(fset *token.FileSet, inputDir, out string) error {
	visited := map[string]bool{}
	var walk func(files []string) error
	walk = func(files []string) error {
		for _, f := range files {
			parsedIm, err := parser.ParseFile(fset, f, nil, parser.ImportsOnly)
			if err != nil {
				return err
			}
			for _, spec := range parsedIm.Imports {
				p, err := strconv.Unquote(spec.Path.Value)
				if err != nil || p == "" || visited[p] {
					continue
				}
				// Never step outside the case dir: only clean,
				// relative, non-escaping paths are local candidates.
				if strings.HasPrefix(p, "/") || strings.Contains(p, "..") ||
					filepath.ToSlash(filepath.Clean(filepath.FromSlash(p))) != p {
					continue
				}
				dir := filepath.Join(inputDir, filepath.FromSlash(p))
				pkgFiles, err := packageFiles(dir)
				if err != nil {
					continue // not a local package: stdlib or a go-run error
				}
				visited[p] = true
				dst := filepath.Join(out, "gopath", "src", filepath.FromSlash(p))
				if err := os.MkdirAll(dst, 0o755); err != nil {
					return err
				}
				for _, src := range pkgFiles {
					data, err := os.ReadFile(src)
					if err != nil {
						return err
					}
					if err := os.WriteFile(filepath.Join(dst, filepath.Base(src)), data, 0o644); err != nil {
						return err
					}
				}
				if err := walk(pkgFiles); err != nil {
					return err
				}
			}
		}
		return nil
	}
	mainFiles, err := packageFiles(inputDir)
	if err != nil {
		return err
	}
	return walk(mainFiles)
}

type parsedFile struct {
	path string
	file *ast.File
}

func packageFiles(dir string) ([]string, error) {
	files, err := filepath.Glob(filepath.Join(dir, "*.go"))
	if err != nil {
		return nil, err
	}
	out := []string{}
	for _, file := range files {
		if strings.HasSuffix(filepath.Base(file), "_test.go") {
			continue
		}
		out = append(out, file)
	}
	if len(out) == 0 {
		return nil, fmt.Errorf("no non-test Go files in %s", dir)
	}
	return out, nil
}

func parseArgs(raw string) ([]string, error) {
	if raw == "-" {
		return nil, nil
	}
	parts := strings.Split(raw, ",")
	for _, part := range parts {
		if part == "" {
			return nil, fmt.Errorf("empty integer argument in %q", raw)
		}
		// Arguments are VALIDATED here and pasted verbatim into the
		// generated harness as `T(value)` conversions, so the only
		// question this function answers is whether the literal denotes a
		// value some 64-bit Go integer type can hold. The corpus uses BOTH
		// domains: signed rows reach -9223372036854775808
		// (examples/kadane/harness-r-minseed), and — since gallery-campaign
		// extension E1 (docs/gallery-campaign-log/g2.md) — unsigned rows
		// reach 18446744073709551615 (examples/dotprod/harness-r-wrap-u64max),
		// the uint64 wrap region the MACHINE side has always accepted
		// (`--arg-int` parses arbitrary-precision Int in GoLean/CLI.lean).
		// int64 is tried FIRST so every pre-E1 row, negatives included,
		// keeps byte-identical behaviour; uint64 is the fallback that opens
		// only the [2^63, 2^64) half. Anything outside both fails closed
		// here. Note this is deliberately NOT a per-parameter type check:
		// a uint64-only literal handed to an int64 parameter is a Go
		// constant-overflow COMPILE error in the generated harness, caught
		// loudly at the go-run stage by the authority on the question.
		_, errInt := strconv.ParseInt(part, 10, 64)
		if errInt != nil {
			if _, errUint := strconv.ParseUint(part, 10, 64); errUint != nil {
				return nil, fmt.Errorf("invalid integer argument %q: not an int64 (%v) and not a uint64: %w", part, errInt, errUint)
			}
		}
	}
	return parts, nil
}

func pruneUnusedImports(file *ast.File) {
	used := map[string]bool{}
	ast.Inspect(file, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.ImportSpec:
			return false
		case *ast.Ident:
			used[n.Name] = true
		}
		return true
	})

	decls := file.Decls[:0]
	for _, decl := range file.Decls {
		gen, ok := decl.(*ast.GenDecl)
		if !ok || gen.Tok != token.IMPORT {
			decls = append(decls, decl)
			continue
		}

		specs := gen.Specs[:0]
		for _, spec := range gen.Specs {
			importSpec := spec.(*ast.ImportSpec)
			name := importName(importSpec)
			if name == "_" || name == "." || used[name] {
				specs = append(specs, spec)
			}
		}
		if len(specs) > 0 {
			gen.Specs = specs
			decls = append(decls, gen)
		}
	}
	file.Decls = decls
}

func importName(spec *ast.ImportSpec) string {
	if spec.Name != nil {
		return spec.Name.Name
	}
	value, err := strconv.Unquote(spec.Path.Value)
	if err != nil {
		return ""
	}
	return path.Base(value)
}

func formatNode(fset *token.FileSet, node any) ([]byte, error) {
	var buf bytes.Buffer
	if err := printer.Fprint(&buf, fset, node); err != nil {
		return nil, err
	}
	formatted, err := format.Source(buf.Bytes())
	if err != nil {
		return nil, err
	}
	return formatted, nil
}

func harnessSource(fset *token.FileSet, fn *ast.FuncDecl, subject string, argValues []string, expectedStatus string) ([]byte, error) {
	paramTypes, variadic, err := functionParamTypes(fset, fn.Type)
	if err != nil {
		return nil, err
	}
	resultCount := functionResultCount(fn.Type)
	if expectedStatus == "ok" && resultCount == 0 {
		return nil, fmt.Errorf("ok subject %s must return at least one observable value", subject)
	}
	if err := validateArgCount(subject, paramTypes, variadic, argValues); err != nil {
		return nil, err
	}

	args := make([]string, len(argValues))
	for i, value := range argValues {
		typeIndex := i
		if typeIndex >= len(paramTypes) {
			typeIndex = len(paramTypes) - 1
		}
		args[i] = fmt.Sprintf("%s(%s)", paramTypes[typeIndex], value)
	}

	var call strings.Builder
	switch resultCount {
	case 0:
		fmt.Fprintf(&call, "\t%s(%s)\n\t_goleanPrintOk([]any{})\n", subject, strings.Join(args, ", "))
	default:
		names := make([]string, resultCount)
		for i := range names {
			names[i] = fmt.Sprintf("_golean_r%d", i)
		}
		fmt.Fprintf(&call, "\t%s := %s(%s)\n", strings.Join(names, ", "), subject, strings.Join(args, ", "))
		fmt.Fprintf(&call, "\t_goleanValues := []any{}\n")
		for _, name := range names {
			fmt.Fprintf(&call, "\t{\n")
			// &r, not r: passing the result through an `any` parameter
			// COLLAPSES an interface-typed result into its dynamic value,
			// so `reflect` could never see Kind()==Interface and the
			// machine's `{"tag":"interface",…}` shape had no Go
			// counterpart it could ever equal (pre-merge audit
			// 2026-07-31, finding 2). The pointer preserves the STATIC
			// type; Elem() then reports the real kind.
			fmt.Fprintf(&call, "\t\t_goleanValue, _goleanErr := _goleanObservationValue(&%s)\n", name)
			fmt.Fprintf(&call, "\t\tif _goleanErr != nil {\n\t\t\t_goleanPrintError(_goleanErr.Error())\n\t\t\treturn\n\t\t}\n")
			fmt.Fprintf(&call, "\t\t_goleanValues = append(_goleanValues, _goleanValue)\n")
			fmt.Fprintf(&call, "\t}\n")
		}
		fmt.Fprintf(&call, "\t_goleanPrintOk(_goleanValues)\n")
	}

	source := fmt.Sprintf(`package main

import (
	_golean_json "encoding/json"
	_golean_fmt "fmt"
	_golean_math "math"
	_golean_os "os"
	_golean_reflect "reflect"
)

// _goleanObservationValue takes a POINTER to the observed result so the
// result's static type survives: reflect.ValueOf(x) on an interface-typed
// x reports the DYNAMIC value's kind, never reflect.Interface.
func _goleanObservationValue(ptr any) (any, error) {
	return _goleanReflectValue(_golean_reflect.ValueOf(ptr).Elem())
}

func _goleanReflectValue(value _golean_reflect.Value) (any, error) {
	if !value.IsValid() {
		return map[string]any{"tag": "nil"}, nil
	}
	switch value.Kind() {
	case _golean_reflect.Bool:
		return map[string]any{"tag": "bool", "value": value.Bool()}, nil
	// Kind-carrying integer observation (grossmith hunt F15): the reflect
	// KIND (width + signedness; "int8", "uint64", ...) rides beside the
	// value, symmetrically with the machine encoder's IntKind — a
	// kind-defaulting machine bug landing on the right numeric value was
	// invisible to the value-only shape. The defined-type name is NOT
	// emitted (the machine value carries an IntKind only; defined-type
	// identity over ints is observable only through interface boxes, on
	// both sides alike). Uintptr FAILS CLOSED below: the frontend maps
	// uintptr to uint64 (NativeToIR intKindOfName), so the machine side
	// can never answer "uintptr" and the observation could never compare
	// equal — refuse loudly rather than alias the kind away (the exact
	// F15 defect class).
	case _golean_reflect.Int, _golean_reflect.Int8, _golean_reflect.Int16, _golean_reflect.Int32, _golean_reflect.Int64:
		return map[string]any{"tag": "int", "kind": value.Kind().String(), "value": value.Int()}, nil
	case _golean_reflect.Uint, _golean_reflect.Uint8, _golean_reflect.Uint16, _golean_reflect.Uint32, _golean_reflect.Uint64:
		return map[string]any{"tag": "int", "kind": value.Kind().String(), "value": value.Uint()}, nil
	case _golean_reflect.Uintptr:
		return nil, _golean_fmt.Errorf("unsupported Go observation kind uintptr (the frontend maps uintptr to uint64; a kind-visible channel must not alias them)")
	case _golean_reflect.Float64:
		// BIT-pattern observation (floats design note S5/S7): bit-exact
		// modulo NaN canonicalization — NaN payload/sign are platform- and
		// path-dependent and unobservable in the language proper, so both
		// encoders canonicalize; signed zero stays exact. Revisit if
		// math.Float64bits ever enters the supported surface.
		f := value.Float()
		bits := _golean_math.Float64bits(f)
		if f != f {
			bits = 0x7FF8000000000000
		}
		return map[string]any{"tag": "float", "kind": "float64", "bits": bits}, nil
	case _golean_reflect.Float32:
		f := float32(value.Float())
		bits := _golean_math.Float32bits(f)
		if f != f {
			bits = 0x7FC00000
		}
		return map[string]any{"tag": "float", "kind": "float32", "bits": bits}, nil
	case _golean_reflect.String:
		bytes := []int{}
		for _, b := range []byte(value.String()) {
			bytes = append(bytes, int(b))
		}
		return map[string]any{"tag": "string", "bytes": bytes}, nil
	case _golean_reflect.Array:
		values := []any{}
		for i := 0; i < value.Len(); i++ {
			elem, err := _goleanReflectValue(value.Index(i))
			if err != nil {
				return nil, err
			}
			values = append(values, elem)
		}
		return map[string]any{"tag": "array", "values": values}, nil
	case _golean_reflect.Interface:
		// A BOXED value: Go's own model is (dynamic type, value), and the
		// machine reports exactly that. A nil interface is the nil
		// observation (no dynamic type at all).
		if value.IsNil() {
			return map[string]any{"tag": "nil"}, nil
		}
		inner := value.Elem()
		name := inner.Type().Name()
		if name == "" {
			// An UNNAMED dynamic type (*T, []T, map[K]V, func(...)):
			// reflect.Type.Name() is empty, and the observation channel's
			// stated naming contract IS reflect.Type.Name(). Fail closed
			// rather than invent a spelling the machine might or might not
			// agree with.
			return nil, _golean_fmt.Errorf("unsupported Go observation: interface holding unnamed dynamic type %%s", inner.Type())
		}
		innerValue, err := _goleanReflectValue(inner)
		if err != nil {
			return nil, err
		}
		return map[string]any{"tag": "interface", "dynamic": name, "value": innerValue}, nil
	case _golean_reflect.Struct:
		fields := []any{}
		typ := value.Type()
		for i := 0; i < value.NumField(); i++ {
			fieldValue, err := _goleanReflectValue(value.Field(i))
			if err != nil {
				return nil, err
			}
			fields = append(fields, map[string]any{"name": typ.Field(i).Name, "value": fieldValue})
		}
		return map[string]any{"tag": "struct", "typeName": typ.Name(), "fields": fields}, nil
	default:
		return nil, _golean_fmt.Errorf("unsupported Go observation kind %%s", value.Kind())
	}
}

// The "output" field (stdlib slice 3) is NOT written here: a process cannot
// observe its own fd 2, so the runner captures stderr separately and splices
// the literal in (scripts/diff-coverage inject_output, via --split-stderr).
func _goleanPrintOk(values []any) {
	if err := _golean_json.NewEncoder(_golean_os.Stdout).Encode(map[string]any{"schema": "golean-observation-v1", "status": "ok", "values": values}); err != nil {
		panic(err)
	}
}

func _goleanPrintError(message string) {
	if err := _golean_json.NewEncoder(_golean_os.Stdout).Encode(map[string]any{"schema": "golean-observation-v1", "status": "error", "message": message}); err != nil {
		panic(err)
	}
}

func main() {
%s}
`, call.String())
	return format.Source([]byte(source))
}

func functionParamTypes(fset *token.FileSet, fn *ast.FuncType) ([]string, bool, error) {
	if fn.Params == nil {
		return nil, false, nil
	}
	types := []string{}
	variadic := false
	for i, field := range fn.Params.List {
		typeExpr := field.Type
		if ellipsis, ok := typeExpr.(*ast.Ellipsis); ok {
			if i != len(fn.Params.List)-1 {
				return nil, false, fmt.Errorf("variadic parameter is not last")
			}
			variadic = true
			typeExpr = ellipsis.Elt
		}
		typeText, err := exprString(fset, typeExpr)
		if err != nil {
			return nil, false, err
		}
		count := len(field.Names)
		if count == 0 {
			count = 1
		}
		for j := 0; j < count; j++ {
			types = append(types, typeText)
		}
	}
	return types, variadic, nil
}

func functionResultCount(fn *ast.FuncType) int {
	if fn.Results == nil {
		return 0
	}
	count := 0
	for _, field := range fn.Results.List {
		if len(field.Names) == 0 {
			count++
		} else {
			count += len(field.Names)
		}
	}
	return count
}

func validateArgCount(subject string, paramTypes []string, variadic bool, args []string) error {
	if !variadic && len(args) != len(paramTypes) {
		return fmt.Errorf("subject %s expects %d argument(s), got %d", subject, len(paramTypes), len(args))
	}
	if variadic && len(args) < len(paramTypes)-1 {
		return fmt.Errorf("subject %s expects at least %d argument(s), got %d", subject, len(paramTypes)-1, len(args))
	}
	return nil
}

func exprString(fset *token.FileSet, expr ast.Expr) (string, error) {
	var buf bytes.Buffer
	if err := printer.Fprint(&buf, fset, expr); err != nil {
		return "", err
	}
	return buf.String(), nil
}
