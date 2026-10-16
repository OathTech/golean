package main

// Unit tests for the compiler-directive refusal (directives.go; BUG-127,
// BUG-128; release-readiness rows 38 and 39; RULED [USER] Mike 2026-10-13,
// item 3 agreed, relayed by the [AGENT] coordinator). The corpus rows
// (Corpus/coverage/exec/directives/*, negative/compile/directives/*) pin
// the gc verdicts; this table pins the SCAN: every form gc recognizes,
// the allowlist and its PLACEMENT rules (fix round, review HIGH-1), the
// imported-unit reach, and the shapes that are NOT directives.

import (
	"go/token"
	"strings"
	"testing"
)

const dirMain = "package main\n\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"

func TestCompilerDirectives(t *testing.T) {
	cases := []struct {
		label string
		files map[string]string
		want  []string // nil = accepted; else substrings of the refusal
	}{
		// F2: the review's witnesses.
		{"go:embed (gc 5, the model answered 0)",
			map[string]string{"main.go": "package main\n\nimport _ \"embed\"\n\n//go:embed data.txt\nvar x string\n\nfunc subject() { println(len(x)) }\n\nfunc main() { subject() }\n", "data.txt": "hello"},
			[]string{"file selection in", "main.go:5:1 carries the compiler directive `//go:embed data.txt`", "refuse by name"}},
		{"go:embed with the file ABSENT (gc rejects the package; the frontend exported)",
			map[string]string{"main.go": "package main\n\nimport _ \"embed\"\n\n//go:embed data.txt\nvar x string\n\nfunc subject() { println(len(x)) }\n\nfunc main() { subject() }\n"},
			[]string{"main.go:5:1 carries the compiler directive `//go:embed data.txt`"}},
		{"go:linkname variable (gc's linker rejects; the frontend answered 0)",
			map[string]string{"main.go": "package main\n\nimport _ \"unsafe\"\n\n//go:linkname x runtime.zerobase\nvar x uintptr\n\nfunc subject() { println(x) }\n\nfunc main() { subject() }\n"},
			[]string{"main.go:5:1 carries the compiler directive `//go:linkname x runtime.zerobase`"}},
		{"go:linkname function gc ACCEPTS (refused by ruling, no modelling)",
			map[string]string{"main.go": "package main\n\nimport _ \"unsafe\"\n\n//go:linkname seven example.org/x.seven\nfunc seven() int { return 7 }\n\nfunc subject() { println(seven()) }\n\nfunc main() { subject() }\n"},
			[]string{"carries the compiler directive `//go:linkname seven example.org/x.seven`"}},
		{"go:linkname without \"unsafe\" (gc: missing function body — the directive refuses first)",
			map[string]string{"main.go": "package main\n\n//go:linkname f\nfunc f()\n\nfunc main() {}\n"},
			[]string{"main.go:3:1 carries the compiler directive `//go:linkname f`"}},
		// F3: runtime settings.
		{"go:debug panicnil=1 before the package clause (gc prints true, the model false)",
			map[string]string{"main.go": "//go:debug panicnil=1\npackage main\n\nfunc f() (r bool) {\n\tdefer func() { r = recover() == nil }()\n\tpanic(nil)\n}\n\nfunc subject() { println(f()) }\n\nfunc main() { subject() }\n"},
			[]string{"main.go:1:1 carries the runtime-setting directive `//go:debug panicnil=1`", "GODEBUG=panicnil=0", "Go 1.26 module defaults"}},
		{"go:debug with a setting gc rejects (unknown //go:debug setting)",
			map[string]string{"main.go": "//go:debug nonexistentSetting=1\n" + dirMain},
			[]string{"carries the runtime-setting directive `//go:debug nonexistentSetting=1`"}},
		{"go:debug after the package clause (the go command ignores it; refused by name anyway)",
			map[string]string{"main.go": "package main\n\n//go:debug panicnil=1\n\nfunc main() {}\n"},
			[]string{"main.go:3:1 carries the runtime-setting directive"}},
		// Line directives: gc honours //line at column 1 and /*line anywhere.
		{"//line at column 1",
			map[string]string{"main.go": "package main\n\n//line other.go:100\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"},
			[]string{"main.go:3:1 carries the line directive `//line other.go:100`"}},
		{"/*line*/ mid-line",
			map[string]string{"main.go": "package main\n\nfunc subject() { /*line other.go:200*/ println(1) }\n\nfunc main() { subject() }\n"},
			[]string{"main.go:3:18 carries the line directive `/*line other.go:200*/`"}},
		{"indented //line (prose to gc; refused by name, stated in the text)",
			map[string]string{"main.go": "package main\n\nfunc subject() {\n\t//line other.go:300\n\tprintln(1)\n}\n\nfunc main() { subject() }\n"},
			[]string{"main.go:4:2 carries the line directive `//line other.go:300`", "column 1"}},
		// Other verbs gc knows: codegen, race instrumentation, wasm — all refused.
		{"go:nosplit", map[string]string{"main.go": "package main\n\n//go:nosplit\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, []string{"carries the compiler directive `//go:nosplit`"}},
		{"go:norace (would hide a race from the -race oracle)", map[string]string{"main.go": "package main\n\n//go:norace\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, []string{"carries the compiler directive `//go:norace`"}},
		{"go:nocheckptr", map[string]string{"main.go": "package main\n\n//go:nocheckptr\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, []string{"carries the compiler directive `//go:nocheckptr`"}},
		{"go:wasmimport", map[string]string{"main.go": "package main\n\n//go:wasmimport env f\nfunc f()\n\nfunc main() {}\n"}, []string{"carries the compiler directive `//go:wasmimport env f`"}},
		{"go:fix (a tool directive gc 1.26 knows; outside the allowlist, refused — widening is a ruling)", map[string]string{"main.go": "package main\n\n//go:fix inline\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, []string{"carries the compiler directive `//go:fix inline`"}},
		{"unknown verb (gc ignores it outside std; over-refused by name)", map[string]string{"main.go": "package main\n\n//go:frobnicate\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, []string{"carries the compiler directive `//go:frobnicate`", "//go:build, //go:noinline, //go:generate"}},
		{"indented //go:noescape inside a body (gc reads directives in any column)", map[string]string{"main.go": "package main\n\nfunc subject() {\n\t//go:noescape\n\tprintln(1)\n}\n\nfunc main() { subject() }\n"}, []string{"main.go:4:2 carries the compiler directive `//go:noescape`"}},
		{"/*go:embed*/ block form is prose to gc (scanner.go fullComment hands only /*line to the pragma handler; measured: the variable stays empty, gc prints 0)", map[string]string{"main.go": "package main\n\n/*go:embed data.txt*/\nvar x string\n\nfunc main() { println(len(x)) }\n"}, nil},
		{"/*go:noinline*/ after code (a14: prose to gc, measured 1)", map[string]string{"main.go": "package main\n\nfunc f() int { return 1 } /*go:noinline*/\n\nfunc main() { println(f()) }\n"}, nil},
		// The imported-unit reach: the same site serves load.go parseLocal.
		{"directive in a case-local imported package",
			map[string]string{
				"main.go":    "package main\n\nimport \"lib\"\n\nfunc subject() { println(lib.V()) }\n\nfunc main() { subject() }\n",
				"lib/lib.go": "package lib\n\nimport _ \"unsafe\"\n\n//go:linkname V example.org/x.V\nfunc V() int { return 1 }\n",
			},
			[]string{"file selection in", "lib.go:5:1 carries the compiler directive `//go:linkname V example.org/x.V`"}},
		// The allowlist, and shapes that are not directives.
		{"go:noinline (allowed: optimisation only)", map[string]string{"main.go": "package main\n\n//go:noinline\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, nil},
		{"go:generate (allowed: never read by the compiler)", map[string]string{"main.go": "package main\n\n//go:generate echo hi\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, nil},
		{"go:build with an inert custom tag (allowed: the langversion.go policy judges it)", map[string]string{"main.go": "//go:build !with_tla\n\n" + dirMain}, nil},
		// PLACEMENT (fix round, review HIGH-1; gc go1.26.5 measured on every
		// shape: «misplaced compiler directive» for each refusal below, the
		// printed value for each acceptance). The reviewer's probes a1–a12
		// and the lane's a13–a20.
		{"a5: go:build after the package clause (gc: misplaced; was wrongly accepted)", map[string]string{"main.go": "package main\n\n//go:build ignore\n\nfunc subject() int { return 5 }\n\nfunc main() { println(subject()) }\n"}, []string{"main.go:3:1 carries the compiler directive `//go:build ignore` after the package clause", "misplaced compiler directive"}},
		{"a8: go:build after code on the same line", map[string]string{"main.go": "package main\n\nfunc main() { x := 1 //go:build foo\n\tprintln(x)\n}\n"}, []string{"main.go:3:22 carries the compiler directive `//go:build foo` after code on the same line"}},
		{"a3: go:generate after code on the same line", map[string]string{"main.go": "package main\n\nfunc main() { println(1) } //go:generate echo hi\n"}, []string{"main.go:3:28 carries the compiler directive `//go:generate echo hi` after code on the same line"}},
		{"a4: go:noinline after code on the same line", map[string]string{"main.go": "package main\n\nfunc f() int { return 1 } //go:noinline\n\nfunc main() { println(f()) }\n"}, []string{"carries the compiler directive `//go:noinline` after code on the same line"}},
		{"a19: an unknown verb after code (refused as outside the allowlist; gc: misplaced)", map[string]string{"main.go": "package main\n\nfunc main() { println(1) } //go:frobnicate\n"}, []string{"carries the compiler directive `//go:frobnicate`"}},
		{"a1: go:noinline inside a body", map[string]string{"main.go": "package main\n\nfunc main() {\n\t//go:noinline\n\tprintln(1)\n}\n"}, []string{"main.go:4:2 carries the compiler directive `//go:noinline` that no func or method declaration follows"}},
		{"a1s: go:noinline inside the subject's body (the model answered ok 1)", map[string]string{"main.go": "package main\n\nfunc subject() int {\n\t//go:noinline\n\treturn 1\n}\n\nfunc main() { println(subject()) }\n"}, []string{"that no func or method declaration follows"}},
		{"a2: go:noinline before a var", map[string]string{"main.go": "package main\n\n//go:noinline\nvar x = 1\n\nfunc main() { println(x) }\n"}, []string{"main.go:3:1 carries the compiler directive `//go:noinline` that no func or method declaration follows"}},
		{"a7: go:noinline before a type", map[string]string{"main.go": "package main\n\n//go:noinline\ntype T int\n\nfunc main() { println(T(1)) }\n"}, []string{"that no func or method declaration follows"}},
		{"a18: go:noinline before a func TYPE declaration", map[string]string{"main.go": "package main\n\n//go:noinline\ntype F func() int\n\nfunc main() { var f F; println(f == nil) }\n"}, []string{"that no func or method declaration follows"}},
		{"a11: go:noinline before an import", map[string]string{"main.go": "package main\n\n//go:noinline\nimport \"strings\"\n\nfunc main() { println(strings.ToUpper(\"a\")) }\n"}, []string{"that no func or method declaration follows"}},
		{"a6: go:noinline at the end of the file", map[string]string{"main.go": "package main\n\nfunc main() { println(1) }\n\n//go:noinline\n"}, []string{"main.go:5:1 carries the compiler directive `//go:noinline` that no func or method declaration follows"}},
		{"a13: go:noinline before the package clause", map[string]string{"main.go": "//go:noinline\npackage main\n\nfunc f() int { return 1 }\n\nfunc main() { println(f()) }\n"}, []string{"main.go:1:1 carries the compiler directive `//go:noinline` that no func or method declaration follows"}},
		{"a17: go:noinline inside a var block", map[string]string{"main.go": "package main\n\nvar (\n\t//go:noinline\n\tx = 1\n)\n\nfunc main() { println(x) }\n"}, []string{"that no func or method declaration follows"}},
		{"a9: go:noinline on a method (gc 2)", map[string]string{"main.go": "package main\n\ntype T int\n\n//go:noinline\nfunc (t T) M() int { return int(t) }\n\nfunc main() { println(T(2).M()) }\n"}, nil},
		{"a12: go:noinline, a blank line, then the func (gc 1)", map[string]string{"main.go": "package main\n\n//go:noinline\n\nfunc f() int { return 1 }\n\nfunc main() { println(f()) }\n"}, nil},
		{"a16: go:noinline, a doc comment, then the func (gc 1)", map[string]string{"main.go": "package main\n\n//go:noinline\n// f is documented after the directive.\nfunc f() int { return 1 }\n\nfunc main() { println(f()) }\n"}, nil},
		{"a10: go:generate inside a body (no flag: never misplaced on its own line; gc 1)", map[string]string{"main.go": "package main\n\nfunc main() {\n\t//go:generate echo hi\n\tprintln(1)\n}\n"}, nil},
		{"a15: go:generate before the package clause (gc 1)", map[string]string{"main.go": "//go:generate echo hi\npackage main\n\nfunc main() { println(1) }\n"}, nil},
		{"indented go:noinline on its own line before a func inside nothing (top level, tab-indented: gc's blank flag holds)", map[string]string{"main.go": "package main\n\n\t//go:noinline\nfunc f() int { return 1 }\n\nfunc main() { println(f()) }\n"}, nil},
		{"`// go:embed` with a blank is prose, not a directive", map[string]string{"main.go": "package main\n\n// go:embed data.txt is what a directive would look like\nvar x string\n\nfunc subject() { println(len(x)) }\n\nfunc main() { subject() }\n"}, nil},
		{"`//golang` prefix is not go:", map[string]string{"main.go": "package main\n\n//golang: not a directive\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, nil},
		{"`// line` with a blank is prose", map[string]string{"main.go": "package main\n\n// line 3 of this file\nfunc subject() { println(1) }\n\nfunc main() { subject() }\n"}, nil},
		{"a string literal containing //go:embed is not a comment", map[string]string{"main.go": "package main\n\nvar x = \"//go:embed data.txt\"\n\nfunc subject() { println(len(x)) }\n\nfunc main() { subject() }\n"}, nil},
	}
	for _, c := range cases {
		t.Run(c.label, func(t *testing.T) {
			dir := writeDir(t, c.files)
			_, err := lowerDir(t, dir)
			if c.want == nil {
				if err != nil {
					t.Fatalf("expected acceptance, got: %v", err)
				}
				return
			}
			if err == nil {
				t.Fatalf("expected a refusal naming %q", c.want)
			}
			msg := err.Error()
			if !strings.HasPrefix(msg, "native frontend unsupported: file selection in ") {
				t.Fatalf("a directive refusal must be a file-selection refusal (the negative leg's rejection shape), got: %v", err)
			}
			for _, w := range c.want {
				if !strings.Contains(msg, w) {
					t.Fatalf("refusal %q does not name %q", msg, w)
				}
			}
		})
	}
}

// The scan is one site for the main package and every imported unit:
// selectPackageFiles itself refuses, before any type-check.
func TestCompilerDirectivesAtSelection(t *testing.T) {
	dir := writeDir(t, map[string]string{"main.go": "package main\n\n//go:embed data.txt\nvar x string\n"})
	_, err := selectPackageFiles(token.NewFileSet(), dir)
	if err == nil || !strings.Contains(err.Error(), "carries the compiler directive `//go:embed data.txt`") {
		t.Fatalf("selectPackageFiles must refuse the directive itself: %v", err)
	}
}

// The allowlist is exactly the ruled set.
func TestCompilerDirectiveAllowlist(t *testing.T) {
	want := []string{"go:build", "go:generate", "go:noinline"}
	if len(allowedDirectiveVerbs) != len(want) {
		t.Fatalf("allowlist has %d verbs, want %d (%v) — widening is a ruling, not an edit", len(allowedDirectiveVerbs), len(want), want)
	}
	for _, v := range want {
		if _, ok := allowedDirectiveVerbs[v]; !ok {
			t.Fatalf("allowlist lacks %s", v)
		}
	}
}
