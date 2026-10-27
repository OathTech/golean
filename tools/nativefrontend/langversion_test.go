package main

import (
	"go/build/constraint"
	"os"
	"path/filepath"
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
	// The policy over a SELECTED file's bytes (judgeSelectedFileConstraints,
	// the site fileselect.go runs after go/build selected the file). A
	// custom-tags-only constraint that is FALSE cannot describe a selected
	// file, so that arm refuses as a disagreement with go/build's verdict —
	// never as «the oracle would exclude the file» (BUG-216's false claim).
	cases := []struct {
		name    string
		src     string
		wantErr string // "" = accepted
	}{
		{"no constraint", "package p\n\nfunc F() {}\n", ""},
		{"custom tag negated, included (the raftsubject form)",
			"//go:build !with_tla\n\npackage p\n", ""},
		{"custom tag, excluded (the ignore fail-open, probe p5): a selected file cannot carry it",
			"//go:build ignore\n\npackage p\n", "go/build's own verdict disagree"},
		{"platform tag, even though included here",
			"//go:build linux\n\npackage p\n", "reserved tag \"linux\""},
		{"version directive (probe p7 class)",
			"//go:build go1.21\n\npackage p\n", "reserved tag \"go1.21\""},
		{"legacy plus-build, honoured (a blank line follows)",
			"// +build ignore\n\npackage p\n", "go/build's own verdict disagree"},
		{"reserved tag hidden in a satisfied OR branch",
			"//go:build !with_tla || windows\n\npackage p\n", "reserved tag \"windows\""},
		{"goexperiment ToolTag, negated (audit T3-1: oracle excludes, we lowered)",
			"//go:build !goexperiment.greenteagc\n\npackage p\n", "reserved tag \"goexperiment.greenteagc\""},
		{"microarch ToolTag (audit T3-1, same class)",
			"//go:build amd64.v1\n\npackage p\n", "reserved tag \"amd64.v1\""},
		{"microarch ToolTag, non-vN capability shape",
			"//go:build !386.sse2\n\npackage p\n", "reserved tag \"386.sse2\""},
		{"dotted custom tag with a non-arch prefix stays custom",
			"//go:build !myorg.internal\n\npackage p\n", ""},
		{"prose mention after the package clause is not a constraint",
			"package p\n\n// this doc talks about //go:build ignore in prose\nfunc F() {}\n", ""},
		// BUG-216: the four shapes go/build IGNORES a `+build` line in — the
		// S20 sweep's probes a13, a14, a15, a16b — are prose here too.
		{"BUG-216 a13: +build under a //go:build line (the //go:build line controls)",
			"//go:build !sweepfoo\n// +build ignore\n\npackage p\n", ""},
		{"BUG-216 a14: +build with no blank line before the package clause",
			"// +build ignore\npackage p\n", ""},
		{"BUG-216 a15: +build inside a /* */ block",
			"/*\n// +build ignore\n*/\n\npackage p\n", ""},
		{"BUG-216 a16b: +build after a /* */ block",
			"/* a block comment */\n\n// +build ignore\n\npackage p\n", ""},
		// The port's other branches, measured on gc 2026-10-27 (the lane's
		// probes h1–h13): a //go:build line inside a block is ignored (h1),
		// after a block it controls (h2), a reserved tag in an ignored
		// placement is prose (h12, h13), a leading BOM is dropped (h8).
		{"h1: //go:build inside a /* */ block is ignored", "/*\n//go:build ignore\n*/\n\npackage p\n", ""},
		{"h2: //go:build after a /* */ block controls", "/* c */\n\n//go:build ignore\n\npackage p\n", "go/build's own verdict disagree"},
		{"h11: //go:build after an honoured-looking +build line wins", "// +build ignore\n\n//go:build !sweepfoo\n\npackage p\n", ""},
		{"h12: a reserved +build tag in an ignored placement is prose", "// +build linux\npackage p\n", ""},
		{"h13: a reserved //go:build tag inside a block is prose", "/*\n//go:build linux\n*/\n\npackage p\n", ""},
		{"h8: a BOM before an inert +build line", "\xef\xbb\xbf// +build !sweepfoo\n\npackage p\n", ""},
		{"a BOM before a reserved //go:build line (go/build strips the BOM)", "\xef\xbb\xbf//go:build linux\n\npackage p\n", "reserved tag \"linux\""},
		{"h9: an indented //go:build line is honoured (go/build trims the line)", "  //go:build linux\n\npackage p\n", "reserved tag \"linux\""},
		{"two //go:build lines: go/build's own error", "//go:build a\n//go:build b\n\npackage p\n", "multiple //go:build comments"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := judgeSelectedFileConstraints("probe.go", []byte(tc.src))
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

// The header port (buildheader.go) against go/build itself: for every
// shape, the lines honouredConstraintLines returns must evaluate (with
// every custom tag unset — the pinned context sets no -tags) to the SAME
// verdict go/build's MatchFile reaches for a file with that content under
// the pinned context, and the lines must be the ones go/build used.
func TestHonouredConstraintLinesAgreeWithGoBuild(t *testing.T) {
	shapes := map[string]string{
		"plain":                      "package p\n",
		"gobuild-ignore":             "//go:build ignore\n\npackage p\n",
		"gobuild-no-blank":           "//go:build ignore\npackage p\n",
		"plusbuild-ignore":           "// +build ignore\n\npackage p\n",
		"plusbuild-no-blank":         "// +build ignore\npackage p\n",
		"plusbuild-under-gobuild":    "//go:build !t\n// +build ignore\n\npackage p\n",
		"plusbuild-in-block":         "/*\n// +build ignore\n*/\n\npackage p\n",
		"plusbuild-after-block":      "/* c */\n\n// +build ignore\n\npackage p\n",
		"gobuild-in-block":           "/*\n//go:build ignore\n*/\n\npackage p\n",
		"gobuild-after-block":        "/* c */\n\n//go:build ignore\n\npackage p\n",
		"plusbuild-doc-blank":        "// +build ignore\n// doc\n\npackage p\n",
		"plusbuild-blank-doc":        "// +build ignore\n\n// doc\npackage p\n",
		"plusbuild-two-lines":        "// +build a\n// +build !t\n\npackage p\n",
		"plusbuild-two-lines-both":   "// +build !a\n// +build !t\n\npackage p\n",
		"plusbuild-empty":            "// +build\n\npackage p\n",
		"plusbuild-unparseable":      "// +build a&&b\n\npackage p\n",
		"bom-gobuild-ignore":         "\xef\xbb\xbf//go:build ignore\n\npackage p\n",
		"bom-plusbuild-inert":        "\xef\xbb\xbf// +build !t\n\npackage p\n",
		"gobuild-indented":           "  //go:build ignore\n\npackage p\n",
		"gobuild-tab":                "//go:build\tignore\n\npackage p\n",
		"gobuild-after-plusbuild":    "// +build ignore\n\n//go:build !t\n\npackage p\n",
		"gobuild-crlf":               "//go:build ignore\r\n\r\npackage p\r\n",
		"gobuild-in-comment-group":   "// Copyright\n//\n//go:build ignore\n\npackage p\n",
		"star-slash-then-gobuild":    "/* a */ //go:build ignore\n\npackage p\n",
		"block-closes-then-gobuild":  "/* a\n*/ //go:build ignore\n\npackage p\n",
		"plusbuild-before-gobuild":   "// +build !t\n\n//go:build ignore\n\npackage p\n",
		"doc-then-plusbuild-no-blank": "// doc\n// +build ignore\npackage p\n",
	}
	ctxt := pinnedBuildContext()
	for name, src := range shapes {
		t.Run(name, func(t *testing.T) {
			dir := t.TempDir()
			if err := os.WriteFile(filepath.Join(dir, "f.go"), []byte(src), 0o644); err != nil {
				t.Fatal(err)
			}
			want, err := ctxt.MatchFile(dir, "f.go")
			if err != nil {
				t.Fatalf("go/build MatchFile: %v", err)
			}
			lines, err := honouredConstraintLines([]byte(src))
			if err != nil {
				t.Fatalf("honouredConstraintLines: %v", err)
			}
			got := true
			for _, line := range lines {
				expr, err := constraint.Parse(line)
				if err != nil {
					t.Fatalf("an honoured line must parse (go/build ignores one that does not): %q: %v", line, err)
				}
				if !expr.Eval(func(string) bool { return false }) {
					got = false
				}
			}
			if got != want {
				t.Fatalf("shape %q: the port says included=%v over lines %q, go/build says %v", name, got, lines, want)
			}
		})
	}
}
