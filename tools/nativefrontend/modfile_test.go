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
		// DC06 (deep-clean review 2026-10-26, FE-04): the COMPLETE version is
		// judged against the pinned toolchain. gc at go1.26.5 ACCEPTS
		// `go 1.26rc1` (measured: it builds); the scanner refuses the
		// prerelease spelling by name — the fail-closed direction, since no
		// prerelease is measured.
		{"go 1.26rc1 (a prerelease: refused by name since 2026-10-26)", "module example.org/m\n\ngo 1.26rc1\n", "declares go 1.26rc1, a prerelease version"},
		{"go 1.26.5 (the pin itself: accepted)", "module example.org/m\n\ngo 1.26.5\n", ""},
		{"go 1.26.6 (a patch floor above the pin: gc «requires go >= 1.26.6»)", "module example.org/m\n\ngo 1.26.6\n", "requires go >= 1.26.6; the oracle is pinned to go1.26.5"},
		{"go 1.26.99 (the review's probe: exported before 2026-10-26)", "module example.org/m\n\ngo 1.26.99\n", "requires go >= 1.26.99; the oracle is pinned to go1.26.5"},
		// DC06 (FE-03): the grammar is VALIDATED, not skipped. Each shape below
		// was measured against gc (go1.26.5, module mode, GOPROXY=off): the
		// first six are gc rejections (the corpus rows under
		// Corpus/coverage/negative/compile/modules/ pin them on the oracle
		// side); the quoted and `module (` forms gc accepts — refused here as
		// not validated (over-refusal, the fail-closed direction).
		{"module without a path (gc «usage: module module/path»)", "module\ngo 1.26\n", "is not `module module/path`"},
		{"repeated module (gc «repeated module statement»)", "module first\nmodule second\ngo 1.26\n", "repeats the module directive (first and \"module second\")"},
		{"no module directive (gc «missing module declaration»)", "go 1.26\n", "has no module directive"},
		{"unterminated require block (gc «syntax error (unterminated block …)»)", "module test\ngo 1.26\nrequire (\n", "the require block opened at line 3 is not closed before the end of the file"},
		{"malformed require line (gc «usage: require module/path v1.2.3»)", "module test\ngo 1.26\nrequire nonsense\n", "is not `require module/path v1.2.3`"},
		{"malformed require block body (gc «usage: require module/path v1.2.3»)", "module test\ngo 1.26\nrequire (\n\tjunk\n)\n", "is not `require module/path v1.2.3`"},
		{"repeated toolchain (gc «repeated toolchain statement»)", "module test\ngo 1.26\ntoolchain go1.26.5\ntoolchain go1.26.5\n", "repeats the toolchain directive"},
		{"version-less replacement that is not a directory (gc refuses)", "module test\ngo 1.26\nreplace a.b/c => d.e/f\n", "replacement module without version must be directory path"},
		{"retract range without the comma (gc «expected ',' after version»)", "module test\ngo 1.26\nretract [v1.0.0 v1.0.1]\n", "is not `retract v1.2.3 | retract [v1.2.3, v1.2.5]`"},
		{"require with a non-canonical version (refused: not validated)", "module test\ngo 1.26\nrequire a.b/c v1.2\n", "is not `require module/path v1.2.3`"},
		{"quoted module path (gc accepts; refused as not validated)", "module \"test\"\ngo 1.26\n", "carries a quoted token"},
		{"module block (gc accepts; refused as not validated)", "module (\n\ttest\n)\ngo 1.26\n", "a `module (` block is not validated"},
		{"a parenthesis inside a block body", "module test\ngo 1.26\nrequire (\n\ta.b/c v1.0.0 (\n)\n", "has a parenthesis among its require arguments"},
		{"replace with a versioned directory target, exclude, pseudo-version: accepted", "module test\ngo 1.26\nreplace a.b/c v1.0.0 => d.e/f v1.0.0\nexclude a.b/c v0.0.0-20240101000000-abcdef123456\nrequire x.y/z v2.0.0+incompatible\n", ""},
		{"go 1.21 — the review's probe (gc 9, GoLean 3)", "module example.org/audit\n\ngo 1.21\n", "go.mod declares go 1.21; GoLean implements the Go 1.26 language only"},
		{"go 1.25", "module example.org/m\n\ngo 1.25\n", "declares go 1.25; GoLean implements the Go 1.26 language only"},
		{"go 1.27 (newer than the pin is foreign too)", "module example.org/m\n\ngo 1.27\n", "declares go 1.27; GoLean implements the Go 1.26 language only"},
		{"no go directive (the go command assumes go 1.16)", "module example.org/m\n", "has no go directive"},
		{"repeated go directive", "module example.org/m\n\ngo 1.26\ngo 1.21\n", "repeats the go directive"},
		{"malformed go directive", "module example.org/m\n\ngo\n", "malformed go directive"},
		{"unparseable version (refused at the grammar: x/mod's GoVersionRE)", "module example.org/m\n\ngo banana\n", "malformed go directive"},
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
		{"toolchain default: gc drops it and refuses the build («updates to go.mod needed»)", "module example.org/m\n\ngo 1.26\n\ntoolchain default\n", "names toolchain default, which gc drops as redundant"},
		{"malformed toolchain directive", "module example.org/m\n\ngo 1.26\n\ntoolchain\n", "malformed toolchain directive"},
		{"go token inside a require block is not the go directive (block skipped), go 1.26 outside it", "module example.org/m\n\nrequire (\n\tgo v0.0.0\n)\n\ngo 1.26\n", ""},
		// Train-19 shake review F2 (2026-10-26; [USER] ruling relayed: gc's
		// condition plus the pin policy; lane frontend/workspace-and-oracle-1026).
		// gc DROPS a toolchain line that is `default`, the go line's own
		// version or below go1.21 (modload WriteGoMod) and under -mod=readonly
		// refuses to build («updates to go.mod needed; to update it: go mod
		// tidy»); a name outside `go1…`/`default` is a parse error. Each shape
		// below was measured on gc go1.26.5 (module mode, GOPROXY=off,
		// GOTOOLCHAIN=local). The review's probe EXPORTED before this.
		{"go 1.26.5 + toolchain go1.26.5 (the review's probe: gc «updates to go.mod needed»)", "module test\ngo 1.26.5\ntoolchain go1.26.5\n", "names toolchain go1.26.5, the go line's own version (go 1.26.5)"},
		{"go 1.26 + toolchain go1.26 (equal without a patch: gc refuses the same way)", "module test\ngo 1.26\ntoolchain go1.26\n", "names toolchain go1.26, the go line's own version (go 1.26)"},
		{"toolchain go1.20.0 (below go1.21: gc drops it and refuses)", "module test\ngo 1.26\ntoolchain go1.20.0\n", "names toolchain go1.20.0, below go1.21"},
		{"toolchain local (gc «invalid toolchain version 'local': must match format go1.23.0 or default»)", "module test\ngo 1.26\ntoolchain local\n", "invalid toolchain version 'local'"},
		{"toolchain go1.26.4 (gc keeps it and builds; refused by the pin policy)", "module test\ngo 1.26\ntoolchain go1.26.4\n", "names toolchain go1.26.4; the oracle is pinned to go1.26.5"},
		{"toolchain go1.26.6 above the pin (inert under GOTOOLCHAIN=local, gc builds; refused by the pin policy)", "module test\ngo 1.26.5\ntoolchain go1.26.6\n", "names toolchain go1.26.6; the oracle is pinned to go1.26.5"},
		{"go 1.26.4 + toolchain go1.26.5: accepted (gc keeps it: the pin above the go line)", "module test\ngo 1.26.4\ntoolchain go1.26.5\n", ""},
		{"go 1.26.0 + toolchain go1.26.5: accepted", "module test\ngo 1.26.0\ntoolchain go1.26.5\n", ""},
		{"toolchain before the go line: judged after the scan, accepted", "module test\ntoolchain go1.26.5\ngo 1.26\n", ""},
		{"go 1.26.6 + toolchain go1.26.5: the floor refusal, gc's «requires go >= 1.26.6»", "module test\ngo 1.26.6\ntoolchain go1.26.5\n", "requires go >= 1.26.6; the oracle is pinned to go1.26.5"},
		{"toolchain () (gc «unknown block type: toolchain»)", "module test\ngo 1.26\ntoolchain ()\n", "unknown block type: toolchain"},
		{"go () (gc «unknown block type: go»)", "module test\ngo ()\n", "unknown block type: go"},
		// Review F5: an EMPTY block on one line is gc's grammar (measured: every
		// accepted verb builds in this form); it was refused as «has a
		// parenthesis where a require argument belongs».
		{"require () — an empty block on one line: accepted", "module test\ngo 1.26\nrequire ()\n", ""},
		{"require ( ) with a blank and a trailing comment: accepted", "module test\ngo 1.26\nrequire ( ) // nothing\n", ""},
		{"exclude (), replace (), retract (), tool (), ignore (): accepted", "module test\ngo 1.26\nexclude ()\nreplace ()\nretract ()\ntool ()\nignore ()\n", ""},
		{"a one-line block WITH a body (gc «usage: require module/path v1.2.3»)", "module test\ngo 1.26\nrequire (a.b/c v1.0.0)\n", "has a parenthesis among its require arguments"},
		{"module () (gc «missing module declaration»)", "module ()\ngo 1.26\n", "a `module (` block is not validated"},
		{"godebug () (an empty block sets nothing; still refused by name, BUG-128)", "module test\ngo 1.26\ngodebug ()\n", "sets godebug (godebug ())"},
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
			// The class prefix the negative corpus's frontend leg reads
			// (scripts/coverage-negative, `frontend=module`).
			if !strings.HasPrefix(err.Error(), "native frontend unsupported: module directive: ") {
				t.Fatalf("refusal %q lacks the `module directive: ` prefix", err.Error())
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

// requireNoWorkspaceAbove fails the test, by name, when the test's own
// directory is already inside a workspace: the acceptance cases below would
// then refuse for a reason that is the machine's, not the code's. A
// precondition failure, never a skip.
func requireNoWorkspaceAbove(t *testing.T, dir string) {
	t.Helper()
	above, err := findGoWork(filepath.Dir(dir))
	if err != nil {
		t.Fatal(err)
	}
	if above != "" {
		t.Fatalf("the test directory %s is inside the workspace %s — run the tests with TMPDIR outside it", dir, above)
	}
}

func wantWorkspaceRefusal(t *testing.T, err error, names ...string) {
	t.Helper()
	if err == nil {
		t.Fatalf("expected a workspace refusal naming %q", names)
	}
	if !strings.HasPrefix(err.Error(), "native frontend unsupported: module directive: ") {
		t.Fatalf("refusal %q lacks the `module directive: ` prefix", err.Error())
	}
	for _, n := range names {
		if !strings.Contains(err.Error(), n) {
			t.Fatalf("refusal %q does not name %q", err.Error(), n)
		}
	}
}

// TestWorkspaceRefusal pins BUG-135 (train-19 shake review F1, 2026-10-26;
// [USER] ruling relayed: refuse by name in the fail-closed direction, keep
// the admitted surface small): a go.work in scope for the lowered
// directory refuses by name, and GOWORK is honoured as the go command
// honours it from the process environment.
func TestWorkspaceRefusal(t *testing.T) {
	// The reviewer's reproduction (docs/reviews/2026-10-26-train19-probes/
	// dc06-modfile/gowork-godebug on branch review/train19-1026), its three
	// files verbatim: with the workspace in scope gc prints true; before
	// this change the frontend exited 0 and the machine answered false,
	// status ok.
	const goMod = "module test\ngo 1.26\n"
	const goWork = "go 1.26\nuse .\ngodebug panicnil=1\n"
	const probeSrc = "package main\n\nfunc probe() (r bool) {\n\tdefer func() { r = recover() == nil }()\n\tpanic(nil)\n}\n\nfunc main() { println(probe()) }\n"

	t.Run("the review's probe: go.work beside go.mod", func(t *testing.T) {
		t.Setenv("GOWORK", "")
		dir := writeDir(t, map[string]string{"main.go": probeSrc, "go.mod": goMod, "go.work": goWork})
		requireNoWorkspaceAbove(t, dir)
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(dir), "is inside the workspace "+filepath.Join(dir, "go.work"), "GOWORK=off")
	})
	t.Run("go.work in a parent directory governs a module below it", func(t *testing.T) {
		t.Setenv("GOWORK", "")
		root := writeDir(t, map[string]string{"go.work": "go 1.26\nuse ./m\n", "m/main.go": probeSrc, "m/go.mod": goMod})
		requireNoWorkspaceAbove(t, root)
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(filepath.Join(root, "m")), "is inside the workspace "+filepath.Join(root, "go.work"))
	})
	t.Run("go.work above a directory WITHOUT a go.mod (gc: «no modules were found in the current workspace»)", func(t *testing.T) {
		t.Setenv("GOWORK", "")
		root := writeDir(t, map[string]string{"go.work": "go 1.26\n", "m/main.go": probeSrc})
		requireNoWorkspaceAbove(t, root)
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(filepath.Join(root, "m")), "is inside the workspace "+filepath.Join(root, "go.work"))
	})
	t.Run("GOWORK=off disables workspace mode, as for the go command (measured: the godebug line no longer applies)", func(t *testing.T) {
		t.Setenv("GOWORK", "off")
		dir := writeDir(t, map[string]string{"main.go": probeSrc, "go.mod": goMod, "go.work": goWork})
		if err := refuseForeignModuleVersion(dir); err != nil {
			t.Fatalf("GOWORK=off: expected acceptance (the go.mod is a go 1.26 module), got %v", err)
		}
	})
	t.Run("GOWORK naming the workspace file: refused by name without reading it", func(t *testing.T) {
		dir := writeDir(t, map[string]string{"main.go": probeSrc, "go.mod": goMod, "go.work": goWork})
		t.Setenv("GOWORK", filepath.Join(dir, "go.work"))
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(dir), "GOWORK="+filepath.Join(dir, "go.work"))
	})
	t.Run("GOWORK naming a missing file (gc: «reading go.work: open …: no such file or directory»): refused", func(t *testing.T) {
		dir := writeDir(t, map[string]string{"main.go": probeSrc, "go.mod": goMod})
		t.Setenv("GOWORK", filepath.Join(dir, "absent", "go.work"))
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(dir), "GOWORK=")
	})
	t.Run("GOWORK relative (gc: «invalid GOWORK: not an absolute path»): refused", func(t *testing.T) {
		dir := writeDir(t, map[string]string{"main.go": probeSrc, "go.mod": goMod})
		t.Setenv("GOWORK", "go.work")
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(dir), "GOWORK=go.work")
	})
	t.Run("a DIRECTORY named go.work is not a workspace file (the go command's rule)", func(t *testing.T) {
		t.Setenv("GOWORK", "")
		dir := writeDir(t, map[string]string{"main.go": probeSrc, "go.mod": goMod, "go.work/.keep": ""})
		requireNoWorkspaceAbove(t, dir)
		if err := refuseForeignModuleVersion(dir); err != nil {
			t.Fatalf("a directory named go.work is not a workspace: expected acceptance, got %v", err)
		}
	})
	t.Run("no go.work in scope: the control", func(t *testing.T) {
		t.Setenv("GOWORK", "")
		dir := writeDir(t, map[string]string{"main.go": probeSrc, "go.mod": goMod})
		requireNoWorkspaceAbove(t, dir)
		if err := refuseForeignModuleVersion(dir); err != nil {
			t.Fatalf("expected acceptance, got %v", err)
		}
	})
	t.Run("the whole pipeline: a case-local package inside a workspace refuses the export naming its go.work", func(t *testing.T) {
		// Per directory, as the go.mod judgement is (load.go parseLocal): the
		// go command, run from main's directory, would not see lib/go.work —
		// the refusal over-approximates by name, the fail-closed direction.
		t.Setenv("GOWORK", "")
		dir := writeDir(t, map[string]string{
			"main.go":     "package main\n\nimport \"lib\"\n\nfunc probe() int { return lib.V() }\n\nfunc main() { println(probe()) }\n",
			"lib/lib.go":  "package lib\n\nfunc V() int { return 1 }\n",
			"lib/go.mod":  "module example.org/lib\n\ngo 1.26\n",
			"lib/go.work": "go 1.26\nuse .\n",
		})
		requireNoWorkspaceAbove(t, dir)
		_, err := lowerDir(t, dir)
		wantWorkspaceRefusal(t, err, filepath.Join("lib", "go.work"))
	})
}
