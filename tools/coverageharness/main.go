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
}

func main() {
	var cfg config
	flag.StringVar(&cfg.input, "input", "", "input Go source")
	flag.StringVar(&cfg.out, "out", "", "output directory")
	flag.StringVar(&cfg.subject, "subject", "", "subject function")
	flag.StringVar(&cfg.args, "args", "-", "comma-separated integer args or -")
	flag.Parse()

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

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, cfg.input, nil, parser.ParseComments)
	if err != nil {
		return err
	}

	var subject *ast.FuncDecl
	decls := file.Decls[:0]
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if ok && fn.Recv == nil && fn.Name.Name == "main" {
			continue
		}
		if ok && fn.Recv == nil && fn.Name.Name == cfg.subject {
			subject = fn
		}
		decls = append(decls, decl)
	}
	file.Decls = decls
	if subject == nil {
		return fmt.Errorf("subject function %q not found in %s", cfg.subject, cfg.input)
	}

	pruneUnusedImports(file)
	source, err := formatNode(fset, file)
	if err != nil {
		return err
	}

	harness, err := harnessSource(fset, subject, cfg.subject, argValues)
	if err != nil {
		return err
	}

	if err := os.RemoveAll(cfg.out); err != nil {
		return err
	}
	if err := os.MkdirAll(cfg.out, 0o755); err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(cfg.out, "main.go"), source, 0o644); err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(cfg.out, "zz_golean_harness.go"), harness, 0o644)
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
		if _, err := strconv.ParseInt(part, 10, 64); err != nil {
			return nil, fmt.Errorf("invalid integer argument %q: %w", part, err)
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

func harnessSource(fset *token.FileSet, fn *ast.FuncDecl, subject string, argValues []string) ([]byte, error) {
	paramTypes, variadic, err := functionParamTypes(fset, fn.Type)
	if err != nil {
		return nil, err
	}
	resultCount := functionResultCount(fn.Type)
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
			fmt.Fprintf(&call, "\t\t_goleanValue, _goleanErr := _goleanObservationValue(%s)\n", name)
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
	_golean_os "os"
	_golean_reflect "reflect"
)

func _goleanObservationValue(value any) (any, error) {
	return _goleanReflectValue(_golean_reflect.ValueOf(value))
}

func _goleanReflectValue(value _golean_reflect.Value) (any, error) {
	if !value.IsValid() {
		return map[string]any{"tag": "nil"}, nil
	}
	switch value.Kind() {
	case _golean_reflect.Bool:
		return map[string]any{"tag": "bool", "value": value.Bool()}, nil
	case _golean_reflect.Int, _golean_reflect.Int8, _golean_reflect.Int16, _golean_reflect.Int32, _golean_reflect.Int64:
		return map[string]any{"tag": "int", "value": value.Int()}, nil
	case _golean_reflect.Uint, _golean_reflect.Uint8, _golean_reflect.Uint16, _golean_reflect.Uint32, _golean_reflect.Uint64, _golean_reflect.Uintptr:
		return map[string]any{"tag": "int", "value": value.Uint()}, nil
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

func _goleanPrintOk(values []any) {
	if err := _golean_json.NewEncoder(_golean_os.Stdout).Encode(map[string]any{"status": "ok", "values": values}); err != nil {
		panic(err)
	}
}

func _goleanPrintError(message string) {
	if err := _golean_json.NewEncoder(_golean_os.Stdout).Encode(map[string]any{"status": "error", "message": message}); err != nil {
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
