package main

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
)

const crashHelperName = "zz_golean_crash.go"
const crashHookIdentifier = "_goleanSetupCrash"

func hasCrashHookIdentifier(file *ast.File) bool {
	found := false
	ast.Inspect(file, func(node ast.Node) bool {
		if id, ok := node.(*ast.Ident); ok && id.Name == crashHookIdentifier {
			found = true
		}
		return !found
	})
	return found
}

// Diagnostic oracles keep the semantic input package untouched. Parse only
// to find the true main opening brace; offsets refer to the original bytes,
// so comments, //line directives and every other source byte are preserved.
// The caller retains its original GOPATH for imported local packages.
func copyOraclePackage(input, out string) error {
	if input == "" || out == "" {
		return fmt.Errorf("oracle copy: input directory and --out required")
	}
	files, err := packageFiles(input)
	if err != nil {
		return err
	}
	data := map[string][]byte{}
	mainFile, mainOffset := "", 0
	fset := token.NewFileSet()
	for _, path := range files {
		if filepath.Base(path) == crashHelperName {
			return fmt.Errorf("oracle copy: reserved helper filename collision")
		}
		raw, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		file, err := parser.ParseFile(fset, path, raw, parser.ParseComments)
		if err != nil {
			return err
		}
		if file.Name.Name != "main" {
			return fmt.Errorf("oracle copy: package is not main")
		}
		if hasCrashHookIdentifier(file) {
			return fmt.Errorf("oracle copy: reserved helper identifier collision")
		}
		for _, decl := range file.Decls {
			fn, ok := decl.(*ast.FuncDecl)
			if ok && fn.Recv == nil && fn.Name.Name == "main" {
				if mainFile != "" || fn.Body == nil {
					return fmt.Errorf("oracle copy: duplicate or missing-body main")
				}
				mainFile = path
				mainOffset = fset.PositionFor(fn.Body.Lbrace, false).Offset + 1
			}
		}
		data[path] = raw
	}
	if mainFile == "" {
		return fmt.Errorf("oracle copy: no main entry")
	}
	// A fresh output directory prevents stale files or overwritten semantic
	// inputs from masquerading as the oracle copy. The caller owns its parent.
	if err := os.Mkdir(out, 0755); err != nil {
		return fmt.Errorf("oracle copy: create fresh output directory: %w", err)
	}
	for _, path := range files {
		raw := data[path]
		if path == mainFile {
			var b bytes.Buffer
			b.Write(raw[:mainOffset])
			b.WriteString("\n_goleanSetupCrash();")
			b.Write(raw[mainOffset:])
			raw = b.Bytes()
		}
		if err := os.WriteFile(filepath.Join(out, filepath.Base(path)), raw, 0644); err != nil {
			return err
		}
	}
	return os.WriteFile(filepath.Join(out, crashHelperName), []byte(crashHelperSource), 0644)
}

// Oracle-only setup: no recover/defer wrapper, and no model/frontend input
// includes this file. The runner creates/resets both files before each run.
// SetCrashOutput duplicates the fd; the original is closed before the subject.
// Exit 78 is a setup failure, never an observation of subject behavior.
const crashHelperSource = `package main

import (
	_golean_os "os"
	_golean_debug "runtime/debug"
)

func _goleanSetupCrash() {
	f, err := _golean_os.OpenFile("oracle.crash", _golean_os.O_WRONLY|_golean_os.O_TRUNC, 0600)
	if err != nil { _golean_os.Exit(78) }
	if err := _golean_debug.SetCrashOutput(f, _golean_debug.CrashOptions{}); err != nil { _golean_os.Exit(78) }
	if err := f.Close(); err != nil { _golean_os.Exit(78) }
	if err := _golean_os.WriteFile("oracle.registered", []byte("registered\n"), 0600); err != nil { _golean_os.Exit(78) }
}
`
