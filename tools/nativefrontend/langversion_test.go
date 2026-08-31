package main

import (
	"go/ast"
	"go/parser"
	"go/token"
	"strings"
	"testing"
)

func TestPinnedLangVersionFromEmbeddedTable(t *testing.T) {
	lang, err := pinnedLangVersion()
	if err != nil {
		t.Fatalf("pinnedLangVersion: %v", err)
	}
	// The language version must be the Lang() of the toolchain named in
	// the embedded table header (itself gate-checked against
	// baselines/go-oracle-pin), not a hand-written constant — so assert
	// the shape, not a second copy of the pin.
	if !strings.HasPrefix(lang, "go1.") || strings.Count(lang, ".") != 1 {
		t.Fatalf("pinnedLangVersion = %q, want a goX.Y language version", lang)
	}
}

func TestBuildConstraintRefusal(t *testing.T) {
	cases := []struct {
		name    string
		src     string
		wantErr string // "" = accepted
	}{
		{"no constraint", "package p\n\nfunc F() {}\n", ""},
		{"custom tag negated, included (the raftsubject form)",
			"//go:build !with_tla\n\npackage p\n", ""},
		{"custom tag, excluded (the ignore fail-open, probe p5)",
			"//go:build ignore\n\npackage p\n", "EXCLUDED by build constraint"},
		{"platform tag, even though included here",
			"//go:build linux\n\npackage p\n", "reserved tag \"linux\""},
		{"version directive (probe p7 class)",
			"//go:build go1.21\n\npackage p\n", "reserved tag \"go1.21\""},
		{"legacy plus-build",
			"// +build ignore\n\npackage p\n", "build constraint"},
		{"reserved tag hidden in a satisfied OR branch",
			"//go:build !with_tla || windows\n\npackage p\n", "reserved tag \"windows\""},
		{"prose mention after the package clause is not a constraint",
			"package p\n\n// this doc talks about //go:build ignore in prose\nfunc F() {}\n", ""},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			fset := token.NewFileSet()
			f, err := parser.ParseFile(fset, "probe.go", tc.src, parser.ParseComments)
			if err != nil {
				t.Fatalf("parse: %v", err)
			}
			got := refuseBuildConstrainedFiles(fset, []*ast.File{f})
			if tc.wantErr == "" {
				if got != nil {
					t.Fatalf("want accepted, got refusal: %v", got)
				}
				return
			}
			if got == nil {
				t.Fatalf("want refusal containing %q, got acceptance", tc.wantErr)
			}
			if !strings.Contains(got.Error(), tc.wantErr) {
				t.Fatalf("refusal %q does not contain %q", got.Error(), tc.wantErr)
			}
		})
	}
}
