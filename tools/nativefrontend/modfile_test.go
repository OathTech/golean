package main

// Unit tests for the module `go` directive refusal (BUG-109, modfile.go).
// The differential runner CANNOT exercise this: its oracle runs the
// package copy under GO111MODULE=off from a harness-generated directory
// that carries no go.mod (scripts/diff-coverage go_run_oracle;
// tools/coverageharness copies *.go only), so a corpus row with a go.mod
// would test nothing on the oracle side — a fake row. The pin is here,
// plus the scripts/lower-diagnose transcript in
// docs/evidence/2026-09-11_review-boundary/.

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const loopvarSrc = "package main\n\nfunc probe() int {\n\tvar fs []func() int\n\tfor i := 0; i < 3; i++ {\n\t\tfs = append(fs, func() int { return i })\n\t}\n\treturn fs[0]() + fs[1]() + fs[2]()\n}\n\nfunc main() { println(probe()) }\n"

func TestModuleGoDirectiveRefusal(t *testing.T) {
	cases := []struct {
		label string
		gomod string // "" = no go.mod
		want  string // "" = accepted; else a substring of the refusal
	}{
		{"no go.mod: the pinned 1.26 (the corpus's mode)", "", ""},
		{"go 1.26", "module example.org/m\n\ngo 1.26\n", ""},
		{"go 1.26.0 (a toolchain-shaped version; Lang = go1.26)", "module example.org/m\n\ngo 1.26.0\n", ""},
		{"go 1.26rc1 (Lang = go1.26)", "module example.org/m\n\ngo 1.26rc1\n", ""},
		{"go 1.21 — the review's probe (gc 9, GoLean 3)", "module example.org/audit\n\ngo 1.21\n", "go.mod declares go 1.21; GoLean implements the Go 1.26 language only"},
		{"go 1.25", "module example.org/m\n\ngo 1.25\n", "declares go 1.25; GoLean implements the Go 1.26 language only"},
		{"go 1.27 (newer than the pin is foreign too)", "module example.org/m\n\ngo 1.27\n", "declares go 1.27; GoLean implements the Go 1.26 language only"},
		{"no go directive (the go command assumes go 1.16)", "module example.org/m\n", "has no go directive"},
		{"repeated go directive", "module example.org/m\n\ngo 1.26\ngo 1.21\n", "repeats the go directive"},
		{"malformed go directive", "module example.org/m\n\ngo\n", "malformed go directive"},
		{"unparseable version", "module example.org/m\n\ngo banana\n", "cannot parse"},
		{"go directive after a require block (blocks are skipped, the directive still found)", "module example.org/m\n\nrequire (\n\tgo.example/go v1.0.0\n)\n\ngo 1.21\n", "declares go 1.21"},
		{"comment-only go token is not a directive", "module example.org/m\n// go 1.21\ngo 1.26\n", ""},
		// BUG-128 (release-readiness row 39; RULED [USER] 2026-10-13, item 3
		// agreed, relayed): a godebug line or block is refused by name.
		// Before the fix the scanner skipped both silently (measured:
		// `fields[0] != "go"` continued past the line; `godebug (` was
		// taken for a block and its body skipped).
		{"godebug line (BUG-128)", "module example.org/m\n\ngo 1.26\n\ngodebug panicnil=1\n", "sets godebug (godebug panicnil=1)"},
		{"godebug block (BUG-128)", "module example.org/m\n\ngo 1.26\n\ngodebug (\n\tpanicnil=1\n)\n", "sets godebug (godebug ()"},
		{"godebug before the go directive (BUG-128: refused first, by name)", "module example.org/m\n\ngodebug panicnil=1\n\ngo 1.21\n", "sets godebug"},
		// Fix round (review MEDIUM-2): the spellings x/mod's lexer accepts —
		// `(` is its own token — and the verb grammar at the pin. Measured
		// with gc (GO111MODULE=on GOPROXY=off): `godebug(` and a trailing
		// comment are honoured (true); `require(` builds; an unknown verb is
		// «unknown directive: frobnicate»; `toolchain go1.27.0` is inert under
		// GOTOOLCHAIN=local (refused here by name all the same).
		{"godebug( without a blank (gc honours it; was accepted silently)", "module example.org/m\n\ngo 1.26\n\ngodebug(\n\tpanicnil=1\n)\n", "sets godebug (godebug()"},
		{"godebug line with a trailing comment", "module example.org/m\n\ngo 1.26\n\ngodebug panicnil=1 // legacy\n", "sets godebug (godebug panicnil=1 // legacy)"},
		{"godebug default=go1.20", "module example.org/m\n\ngo 1.26\n\ngodebug default=go1.20\n", "sets godebug"},
		{"require( without a blank: accepted, the block skipped", "module example.org/m\n\ngo 1.26\n\nrequire(\n\tgolang.org/x/mod v0.20.0 // indirect\n)\n", ""},
		{"require, exclude, replace, retract, tool, ignore lines: accepted", "module example.org/m\n\ngo 1.26\n\nrequire golang.org/x/mod v0.20.0\nexclude golang.org/x/mod v0.19.0\nreplace golang.org/x/mod => ../mod\nretract [v1.0.0, v1.0.1]\ntool example.org/m/cmd/gen\nignore ./testdata\n", ""},
		{"retract block with a rationale comment: accepted", "module example.org/m\n\ngo 1.26\n\nretract (\n\tv1.0.0 // broken\n\t[v1.1.0, v1.1.2]\n)\n", ""},
		{"unknown directive (the go command: «unknown directive: frobnicate»)", "module example.org/m\n\ngo 1.26\n\nfrobnicate on\n", "does not know (\"frobnicate on\")"},
		{"toolchain naming the pin: accepted", "module example.org/m\n\ngo 1.26\n\ntoolchain go1.26.5\n", ""},
		{"toolchain naming another toolchain: refused by name", "module example.org/m\n\ngo 1.26\n\ntoolchain go1.27.0\n", "names toolchain go1.27.0; the oracle is pinned to go1.26.5"},
		{"toolchain default: refused by name (not the pin's name)", "module example.org/m\n\ngo 1.26\n\ntoolchain default\n", "names toolchain default"},
		{"malformed toolchain directive", "module example.org/m\n\ngo 1.26\n\ntoolchain\n", "malformed toolchain directive"},
		{"go token inside a require block is not the go directive (block skipped), go 1.26 outside it", "module example.org/m\n\nrequire (\n\tgo v0.0.0\n)\n\ngo 1.26\n", ""},
	}
	for _, c := range cases {
		t.Run(c.label, func(t *testing.T) {
			dir := t.TempDir()
			if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(loopvarSrc), 0o644); err != nil {
				t.Fatal(err)
			}
			if c.gomod != "" {
				if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte(c.gomod), 0o644); err != nil {
					t.Fatal(err)
				}
			}
			err := refuseForeignModuleVersion(dir)
			if c.want == "" {
				if err != nil {
					t.Fatalf("expected acceptance, got %v", err)
				}
				return
			}
			if err == nil {
				t.Fatalf("expected a refusal naming %q", c.want)
			}
			if !strings.Contains(err.Error(), c.want) {
				t.Fatalf("refusal %q does not name %q", err.Error(), c.want)
			}
			if !strings.Contains(err.Error(), filepath.Join(dir, "go.mod")) {
				t.Fatalf("refusal %q does not name the go.mod path", err.Error())
			}
		})
	}
}

func TestModuleGoDirectiveWalksUp(t *testing.T) {
	// The go command finds the module root by walking UP; a go.mod in a
	// parent directory governs the package (the lowered directory may be
	// a module's subpackage), and a NESTED go.mod under an imported local
	// package is its own module, judged on its own.
	root := t.TempDir()
	if err := os.WriteFile(filepath.Join(root, "go.mod"), []byte("module example.org/m\n\ngo 1.21\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	sub := filepath.Join(root, "cmd", "app")
	if err := os.MkdirAll(sub, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(sub, "main.go"), []byte(loopvarSrc), 0o644); err != nil {
		t.Fatal(err)
	}
	err := refuseForeignModuleVersion(sub)
	if err == nil || !strings.Contains(err.Error(), "declares go 1.21") {
		t.Fatalf("parent go.mod not found by the walk-up: %v", err)
	}
	// The nearest go.mod wins: a 1.26 go.mod in the subdirectory shadows
	// the parent's 1.21.
	if err := os.WriteFile(filepath.Join(sub, "go.mod"), []byte("module example.org/m/cmd/app\n\ngo 1.26\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := refuseForeignModuleVersion(sub); err != nil {
		t.Fatalf("nearest go.mod (1.26) should win: %v", err)
	}
}

func TestModuleGoDirectiveOnImportedLocalPackage(t *testing.T) {
	// The whole pipeline: main (no go.mod) imports a case-local package
	// whose directory carries its own `go 1.21` go.mod — refused at
	// export naming that go.mod (load.go parseLocal).
	dir := writeDir(t, map[string]string{
		"main.go":    "package main\n\nimport \"lib\"\n\nfunc probe() int { return lib.V() }\n\nfunc main() { println(probe()) }\n",
		"lib/lib.go": "package lib\n\nfunc V() int { return 1 }\n",
		"lib/go.mod": "module example.org/lib\n\ngo 1.21\n",
	})
	_, err := lowerDir(t, dir)
	if err == nil || !strings.Contains(err.Error(), "declares go 1.21; GoLean implements the Go 1.26 language only") {
		t.Fatalf("imported local package's go.mod not judged: %v", err)
	}
	if !strings.Contains(err.Error(), filepath.Join("lib", "go.mod")) {
		t.Fatalf("refusal does not name lib/go.mod: %v", err)
	}
}
