package main

import (
	"go/ast"
	"go/token"
	"strconv"
	"testing"
)

// importName on unaliased imports follows goimports' assumed-name rule
// (audit F4, docs/2026-10-01_intn-pick-audit.md): a major-version suffix
// names the previous element; an alias always wins.
func TestImportNameAssumedName(t *testing.T) {
	for _, tc := range []struct{ alias, path, want string }{
		{"", "math/rand/v2", "rand"},
		{"", "math/rand", "rand"},
		{"", "fmt", "fmt"},
		{"", "encoding/json", "json"},
		{"", "v2", "v2"},
		{"", "example.com/m/v10", "m"},
		{"", "gopkg.in/yaml.v3", "yaml"},
		{"", "example.com/vx", "vx"},
		{"", "example.com/v", "v"},
		{"", "github.com/x/go-cmp", "cmp"},
		{"r", "math/rand/v2", "r"},
		{"_", "math/rand/v2", "_"},
		{".", "math/rand/v2", "."},
	} {
		spec := &ast.ImportSpec{Path: &ast.BasicLit{Kind: token.STRING, Value: strconv.Quote(tc.path)}}
		if tc.alias != "" {
			spec.Name = ast.NewIdent(tc.alias)
		}
		if got := importName(spec); got != tc.want {
			t.Errorf("importName(%q %q) = %q, want %q", tc.alias, tc.path, got, tc.want)
		}
	}
}

// pruneUnusedImports keeps an unaliased math/rand/v2 that is used as
// `rand` (the pre-fix behaviour pruned it as the unused name `v2`).
func TestPruneKeepsUnaliasedMajorVersionImport(t *testing.T) {
	spec := &ast.ImportSpec{Path: &ast.BasicLit{Kind: token.STRING, Value: strconv.Quote("math/rand/v2")}}
	file := &ast.File{
		Name: ast.NewIdent("main"),
		Decls: []ast.Decl{
			&ast.GenDecl{Tok: token.IMPORT, Specs: []ast.Spec{spec}},
			&ast.FuncDecl{Name: ast.NewIdent("f"), Type: &ast.FuncType{Params: &ast.FieldList{}},
				Body: &ast.BlockStmt{List: []ast.Stmt{&ast.ExprStmt{X: &ast.CallExpr{
					Fun: &ast.SelectorExpr{X: ast.NewIdent("rand"), Sel: ast.NewIdent("IntN")}}}}}},
		},
	}
	pruneUnusedImports(file)
	gen, ok := file.Decls[0].(*ast.GenDecl)
	if !ok || gen.Tok != token.IMPORT || len(gen.Specs) != 1 {
		t.Fatalf("unaliased math/rand/v2 used as rand was pruned: decls=%#v", file.Decls)
	}
}
