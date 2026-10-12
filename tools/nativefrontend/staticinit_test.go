package main

// staticinit_test.go — the BUG-061 guard (staticinit.go): the witness
// shape refuses by name, the controls lower, the classifier's arms are
// pinned shape by shape.

import (
	"go/ast"
	"go/parser"
	"go/token"
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

// The classifier, shape by shape. Every WORK expectation here is a
// claim that gc's StaticAssign has no static path for the shape; every
// MAYBE-STATIC one that it may.
func TestBug061InitializerClassifier(t *testing.T) {
	shapes := `package shapes

import (
	"errors"
	"other"
)

type T struct {
	x int
	p *int
}
type T2 struct{ m map[int]int }
type I interface{ M() int }
type MyInt int

func (T) M() int { return 1 }

func one() int   { return 1 }
func two() int   { x := 1; return x }
func ptr() *T    { return &T{} }
func blk() int   { { return 3 } }
func cond() int  { if true { return 1 }; return 2 }
func pair() (int, int) { return 1, 2 }

var (
	C    = 5
	Str  = "s"
	Arr  = [3]int{1, 2, 3}
	Sl   = []string{"a"}
	St   = T{x: 1}
	Nest = []T{{x: 1}, {x: 2}}
	M    = map[int]int{1: 2}
	PM   = &map[int]int{}
	StM  = T2{m: map[int]int{}}
	PtrG = &T{}

	Addr  = &C
	AddrF = &St.x
	AddrI = &Arr[1]
	AddrP = &PtrG.x
	Copy  = Arr
	SCopy = Str
	FCopy = other.V
	FV    = one
	FFV   = other.F
	Lit   = func() int { return 1 }
	ME    = T.M
	MV    = St.M
	Fld   = St.x
	Idx   = Arr[0]
	Bin   = C + Arr[0]
	Neg   = -Arr[0]

	Call1  = one()
	Call2  = two()
	CallP  = ptr()
	CallB  = blk()
	CallC  = cond()
	CallE  = errors.New("x")
	IG     I = T{}
	CallI  = IG.M()
	CallIC = I(T{}).M()
	FVar   = one
	CallFV = FVar()

	Conv    = MyInt(Arr[0])
	ConvC   = MyInt(C)
	ConvI   I = St
	ConvIW  = I(IG)
	ConvNil = (*T)(nil)
	Bytes   = []byte("abc")
	BytesV  = []byte(Str)
	Runes   = []rune("abc")
	S2      = string(Bytes)
	F2I     = float64(Arr[0])
	New     = new(int)
	Mk      = make([]int, 3)
	Len     = len(Sl)

	_ = Arr[0]
	_ = two()
	_ I = T{}
)
`
	want := map[string]initializerKind{
		"C": initConstant, "Str": initConstant,
		"Arr": initMaybeStatic, "Sl": initMaybeStatic, "St": initMaybeStatic, "Nest": initMaybeStatic,
		"M": initWork, "PM": initWork, "StM": initWork, "PtrG": initMaybeStatic,
		"Addr": initMaybeStatic, "AddrF": initMaybeStatic, "AddrI": initMaybeStatic, "AddrP": initWork,
		"Copy": initMaybeStatic, "SCopy": initWork, "FCopy": initWork,
		"FV": initMaybeStatic, "FFV": initMaybeStatic, "Lit": initMaybeStatic, "ME": initMaybeStatic,
		"MV": initWork, "Fld": initWork, "Idx": initWork, "Bin": initWork, "Neg": initWork,
		"Call1": initMaybeStatic, "Call2": initWork, "CallP": initMaybeStatic, "CallB": initMaybeStatic,
		"CallC": initWork, "CallE": initMaybeStatic, "IG": initMaybeStatic, "CallI": initWork,
		"CallIC": initMaybeStatic, "FVar": initMaybeStatic, "CallFV": initWork,
		"Conv": initWork, "ConvC": initMaybeStatic, "ConvI": initMaybeStatic, "ConvIW": initWork,
		"ConvNil": initMaybeStatic, "Bytes": initMaybeStatic, "BytesV": initWork, "Runes": initWork,
		"S2": initWork, "F2I": initWork, "New": initWork, "Mk": initWork, "Len": initWork,
	}
	wantBlank := []initializerKind{initMaybeStatic, initWork, initMaybeStatic}

	withStdlibRoots(t) // the errors.New shape needs the pinned stdlib source
	dir := writeDir(t, map[string]string{
		"main.go":          "package main\n\nimport _ \"shapes\"\n\nfunc main() {}\n",
		"shapes/shapes.go": shapes,
		"other/other.go":   "package other\n\nvar V = 1\n\nfunc F() int { return 1 }\n",
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
	var blanks []initializerKind
	for _, f := range u.files {
		for _, d := range f.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.VAR {
				continue
			}
			for _, s := range gd.Specs {
				vs := s.(*ast.ValueSpec)
				for i, v := range vs.Values {
					name := vs.Names[i].Name
					kind := l.initializerKind(u, v, name == "_")
					if name == "_" {
						blanks = append(blanks, kind)
						continue
					}
					seen[name] = true
					if w, ok := want[name]; !ok {
						t.Errorf("%s: no expectation (got %v)", name, kind)
					} else if kind != w {
						t.Errorf("%s = %s: got %v, want %v", name, exprSourceText(fset, v), kind, w)
					}
				}
			}
		}
	}
	for name := range want {
		if !seen[name] {
			t.Errorf("%s: expectation never exercised", name)
		}
	}
	if len(blanks) != len(wantBlank) {
		t.Fatalf("blank initializers: got %d, want %d", len(blanks), len(wantBlank))
	}
	for i := range blanks {
		if blanks[i] != wantBlank[i] {
			t.Errorf("blank initializer %d: got %v, want %v", i, blanks[i], wantBlank[i])
		}
	}
	// The package-level verdict: `pair()` into two names is certain work
	// on its own (OAS2FUNC), so a package holding only that is CERTAIN.
	certain, maybe := l.sourceInitWork(u)
	if !certain {
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
