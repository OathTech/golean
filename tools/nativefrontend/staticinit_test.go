package main

// staticinit_test.go — the BUG-061 guard (staticinit.go): the witness
// shape refuses by name, the controls lower, the classifier's arms are
// pinned shape by shape.

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

// bug061Program is the pinned witness in miniature (Corpus
// multipkg/init-order-staticinit): rec records; la (blank-imports zq)
// and lb are both ready at step one under gc, and zq's initializer is
// whatever the caller says.
func bug061Program(zq string) map[string]string {
	return map[string]string{
		"main.go":    "package main\n\nimport (\n\t_ \"la\"\n\t_ \"lb\"\n\t\"rec\"\n)\n\nfunc main() { println(rec.Seq) }\n",
		"rec/rec.go": "package rec\n\nvar Seq int\n\nfunc Push(mark int) int {\n\tSeq = Seq*10 + mark\n\treturn Seq\n}\n",
		"la/la.go":   "package la\n\nimport (\n\t_ \"zq\"\n\t\"rec\"\n)\n\nvar V = rec.Push(1)\n",
		"lb/lb.go":   "package lb\n\nimport \"rec\"\n\nvar V = rec.Push(2)\n",
		"zq/zq.go":   zq,
	}
}

func TestBug061OrderSensitiveStaticinitShapeRefuses(t *testing.T) {
	dir := writeDir(t, bug061Program("package zq\n\nvar A = [3]int{1, 2, 3}\n"))
	_, err := lowerDir(t, dir)
	if err == nil {
		t.Fatal("the witness shape lowered: the BUG-061 guard did not fire")
	}
	for _, want := range []string{
		"BUG-061",
		"package(s) zq have no certain initialization work",
		"var A = [3]int{1, 2, 3}",
		"zq/zq.go:3:5",
		"scheduled [lb la main]",
		"pruned [la lb main]",
		"refused by name",
	} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("refusal lacks %q:\n%v", want, err)
		}
	}
}

// The same graph with zq CERTAIN (gc schedules it: an init body, a map
// literal, a call to a multi-statement body) or CONSTANT (pruned under
// both rules) lowers exactly as before the guard.
func TestBug061CertainAndConstantPackagesLower(t *testing.T) {
	for name, zq := range map[string]string{
		"init-body":            "package zq\n\nvar Y int\n\nfunc init() { Y = 5 }\n",
		"map-literal":          "package zq\n\nvar M = map[int]int{1: 2}\n",
		"multi-statement-call": "package zq\n\nvar N = f()\n\nfunc f() int {\n\tx := 1\n\treturn x + 1\n}\n",
		"arithmetic":           "package zq\n\nvar X = 1\nvar Y = X + 1\n",
		"constant":             "package zq\n\nvar A = 5\n",
		"nothing":              "package zq\n\nvar A int\n",
	} {
		t.Run(name, func(t *testing.T) {
			dir := writeDir(t, bug061Program(zq))
			if _, err := lowerDir(t, dir); err != nil {
				t.Fatalf("a certain/constant zq must lower: %v", err)
			}
		})
	}
}

// An uncertain package whose pruning cannot move anybody — imported
// only by main, or a node anyway through a node import — lowers.
func TestBug061InsensitiveUncertainPackagesLower(t *testing.T) {
	t.Run("imported-only-by-main", func(t *testing.T) {
		withStdlibRoots(t) // errors.New lowers through the pinned stdlib source
		dir := writeDir(t, map[string]string{
			"main.go":    "package main\n\nimport (\n\t\"lib\"\n\t\"rec\"\n)\n\nfunc main() { println(rec.Seq, lib.Err) }\n",
			"rec/rec.go": "package rec\n\nvar Seq int\n\nfunc Push(mark int) int {\n\tSeq = Seq*10 + mark\n\treturn Seq\n}\n",
			"lib/lib.go": "package lib\n\nimport \"errors\"\n\nvar Err = errors.New(\"x\")\n",
		})
		if _, err := lowerDir(t, dir); err != nil {
			t.Fatalf("an uncertain package nobody but main imports must lower: %v", err)
		}
	})
	t.Run("node-through-import", func(t *testing.T) {
		// zq imports rec2, which has certain work: zq is a node under
		// every pruning, so la's edge to it is real either way.
		files := bug061Program("package zq\n\nimport _ \"rec2\"\n\nvar A = [3]int{1, 2, 3}\n")
		files["rec2/rec2.go"] = "package rec2\n\nvar N int\n\nfunc init() { N = 1 }\n"
		dir := writeDir(t, files)
		if _, err := lowerDir(t, dir); err != nil {
			t.Fatalf("an uncertain package that is a node through its imports must lower: %v", err)
		}
	})
}

// The classifier, shape by shape, against gc's RECORDED verdicts
// (testdata/staticinit-oracle.tsv, written by scripts/test-staticinit-oracle
// over testdata/staticinit-shapes.go — one package per shape, `go build`,
// the ..inittask record read by `go tool nm -size`). Two assertions:
//
//   - SOUNDNESS: a shape gc folds (`none`) is never classified WORK — the
//     class of error the fix round of 2026-10-12 closed (the review's
//     BLOCKER-1/2: gc's dead-code and declaration rules, []rune literals,
//     nested interface conversions);
//   - PRECISION: a shape gc schedules (`work`) is classified WORK unless it
//     is listed below as deliberately conservative, with its reason.
func TestBug061InitializerClassifier(t *testing.T) {
	withStdlibRoots(t) // errors.New lowers through the pinned stdlib source
	shapes := readTestdataFile(t, "staticinit-shapes.go")
	other := readTestdataFile(t, "staticinit-other.go")
	oracle := readStaticinitOracle(t)
	// Shapes gc schedules that the classifier calls MAYBE-STATIC on
	// purpose: each entry is a precision loss accepted for a reason.
	conservative := map[string]string{}

	dir := writeDir(t, map[string]string{
		"main.go":          "package main\n\nimport _ \"shapes\"\n\nfunc main() {}\n",
		"shapes/shapes.go": shapes,
		"other/other.go":   other,
	})
	fset := token.NewFileSet()
	files, err := selectPackageFiles(fset, dir)
	if err != nil {
		t.Fatal(err)
	}
	l := newLoader(fset, dir)
	if _, err := l.loadProgram(files); err != nil {
		t.Fatal(err)
	}
	u := l.locals["shapes"]
	if u == nil || u.info == nil {
		t.Fatal("shapes unit not loaded")
	}
	seen := map[string]bool{}
	blanks := 0
	for _, f := range u.files {
		for _, d := range f.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.VAR {
				continue
			}
			for _, s := range gd.Specs {
				vs := s.(*ast.ValueSpec)
				names := []string{}
				for _, n := range vs.Names {
					if n.Name == "_" {
						blanks++
						names = append(names, "_"+strconv.Itoa(blanks))
					} else {
						names = append(names, n.Name)
					}
				}
				key := strings.Join(names, ",")
				var kind initializerKind
				var text string
				if len(vs.Names) != len(vs.Values) {
					kind = initWork // the tuple rule (sourceInitWork): certain work
					text = key + " = " + exprSourceText(fset, vs.Values[0])
				} else {
					kind = l.initializerKind(u, vs.Values[0], vs.Names[0].Name == "_")
					text = "var " + vs.Names[0].Name + " = " + exprSourceText(fset, vs.Values[0])
				}
				seen[key] = true
				verdict, recorded := oracle[key]
				if !recorded {
					t.Errorf("%s: not in the recorded oracle — run scripts/test-staticinit-oracle --record", key)
					continue
				}
				switch verdict {
				case "none":
					if kind == initWork {
						t.Errorf("SOUNDNESS %s (%s): gc folds it, the classifier says WORK — a silent wrong order (BUG-061's class)", key, text)
					}
				case "work":
					if kind != initWork {
						if why, ok := conservative[key]; ok {
							t.Logf("conservative %s (%s): %v where gc has work — %s", key, text, kind, why)
						} else {
							t.Errorf("PRECISION %s (%s): gc has work, the classifier says %v (list it as conservative with its reason if intended)", key, text, kind)
						}
					}
				default:
					t.Errorf("%s: unrecognized oracle verdict %q", key, verdict)
				}
			}
		}
	}
	for key := range oracle {
		if !seen[key] {
			t.Errorf("oracle row %s has no shape in the loaded package", key)
		}
	}
	t.Logf("%d shapes checked against the recorded gc verdicts (%d conservative)", len(seen), len(conservative))
	for key := range conservative {
		if !seen[key] {
			t.Errorf("conservative entry %s names no shape", key)
		}
	}
	// The package-level verdict: a tuple spec makes the package CERTAIN.
	if certain, maybe := l.sourceInitWork(u); !certain {
		t.Errorf("shapes has WORK initializers: certain must be true (maybe sites: %d)", len(maybe))
	}
	tupleDir := writeDir(t, map[string]string{
		"main.go":    "package main\n\nimport _ \"tup\"\n\nfunc main() {}\n",
		"tup/tup.go": "package tup\n\nfunc pair() (int, int) { return 1, 2 }\n\nvar A, B = pair()\n",
	})
	fset2 := token.NewFileSet()
	files2, err := selectPackageFiles(fset2, tupleDir)
	if err != nil {
		t.Fatal(err)
	}
	l2 := newLoader(fset2, tupleDir)
	if _, err := l2.loadProgram(files2); err != nil {
		t.Fatal(err)
	}
	if certain, maybe := l2.sourceInitWork(l2.locals["tup"]); !certain || len(maybe) != 0 {
		t.Errorf("`var A, B = pair()` must be certain work: certain=%v maybe=%d", certain, len(maybe))
	}
}

func readTestdataFile(t *testing.T, name string) string {
	t.Helper()
	b, err := os.ReadFile(filepath.Join("testdata", name))
	if err != nil {
		t.Fatal(err)
	}
	return string(b)
}

// readStaticinitOracle reads the recorded gc verdicts: key -> none|work.
func readStaticinitOracle(t *testing.T) map[string]string {
	t.Helper()
	out := map[string]string{}
	for _, line := range strings.Split(readTestdataFile(t, "staticinit-oracle.tsv"), "\n") {
		if line == "" || strings.HasPrefix(line, "#") || line == "key\tverdict" {
			continue
		}
		cols := strings.Split(line, "\t")
		if len(cols) != 2 {
			t.Fatalf("staticinit-oracle.tsv: malformed line %q", line)
		}
		out[cols[0]] = cols[1]
	}
	if len(out) == 0 {
		t.Fatal("staticinit-oracle.tsv: no rows — run scripts/test-staticinit-oracle --record")
	}
	return out
}

func (k initializerKind) String() string {
	switch k {
	case initConstant:
		return "constant"
	case initMaybeStatic:
		return "maybe-static"
	case initWork:
		return "work"
	}
	return "?"
}

// The node fact is unchanged by the classifier: "constant or nothing"
// prunes, anything else is a node — on every shape above.
func TestBug061NodeFactUnchanged(t *testing.T) {
	for name, src := range map[string]string{
		"constant":   "package p\n\nvar A = 5\n",
		"nothing":    "package p\n\nvar A int\n",
		"empty-init": "package p\n\nfunc init() {}\n",
	} {
		t.Run(name, func(t *testing.T) {
			if l, u := loadOne(t, src); l.sourceHasInitWork(u) {
				t.Errorf("%s: must be pruned (no work)", name)
			}
		})
	}
	for name, src := range map[string]string{
		"array-literal": "package p\n\nvar A = [3]int{1, 2, 3}\n",
		"init-body":     "package p\n\nvar A int\n\nfunc init() { A = 1 }\n",
		"map-literal":   "package p\n\nvar A = map[int]int{}\n",
	} {
		t.Run(name, func(t *testing.T) {
			if l, u := loadOne(t, src); !l.sourceHasInitWork(u) {
				t.Errorf("%s: must be a node", name)
			}
		})
	}
}

func loadOne(t *testing.T, src string) (*loader, *sourcePkg) {
	t.Helper()
	dir := writeDir(t, map[string]string{
		"main.go": "package main\n\nimport _ \"p\"\n\nfunc main() {}\n",
		"p/p.go":  src,
	})
	fset := token.NewFileSet()
	files, err := parser.ParseDir(fset, dir, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	var mainFiles []*ast.File
	for _, pkg := range files {
		for _, f := range pkg.Files {
			mainFiles = append(mainFiles, f)
		}
	}
	l := newLoader(fset, dir)
	if _, err := l.loadProgram(mainFiles); err != nil {
		t.Fatal(err)
	}
	return l, l.locals["p"]
}
