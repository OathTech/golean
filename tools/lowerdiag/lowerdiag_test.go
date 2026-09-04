package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"
)

const ledgerPath = "../../docs/language-coverage-ledger.md"

func ledgerText(t *testing.T) string {
	b, err := os.ReadFile(ledgerPath)
	if err != nil {
		t.Fatalf("ledger unreadable: %v", err)
	}
	return string(b)
}

// ledgerHasRow: `| FR-n |` in §4, `| Q-NAME |` in §6.
func ledgerHasRow(ledger, id string) bool {
	return strings.Contains(ledger, "\n| "+id+" |")
}

// TestCausesTableAgreesWithLedger — the causes table cannot drift from the
// ledger: a `rowed` FR/Q id must be a ledger row; a `pending:<branch>` id
// must NOT be (once it lands the flag is stale and must flip to rowed).
func TestCausesTableAgreesWithLedger(t *testing.T) {
	cs, err := loadCauses(causesTSV)
	if err != nil {
		t.Fatal(err)
	}
	ledger := ledgerText(t)
	for _, c := range cs {
		isID := strings.HasPrefix(c.FR, "FR-") || strings.HasPrefix(c.FR, "Q-")
		if !isID {
			continue
		}
		has := ledgerHasRow(ledger, c.FR)
		switch {
		case c.Status == "rowed" && !has:
			t.Errorf("cause %s cites %s as rowed, but the ledger has no `| %s |` row", c.ID, c.FR, c.FR)
		case strings.HasPrefix(c.Status, "pending:") && has:
			t.Errorf("cause %s marks %s %s, but the ledger HAS the row now — flip the status to rowed", c.ID, c.FR, c.Status)
		}
	}
}

// Red-first witness for the check above: an FR id the ledger does not row,
// claimed as rowed, is caught.
func TestCausesTableCatchesAnUnrowedFR(t *testing.T) {
	ledger := ledgerText(t)
	bogus := "FR-999"
	if ledgerHasRow(ledger, bogus) {
		t.Fatalf("test premise broken: the ledger rows %s", bogus)
	}
	src := "id\tfr\tstatus\tscope\tpattern\tkey\tdiagnosis\nbogus\t" + bogus + "\trowed\tdecl\tbogus text\t-\ta row the ledger lacks\n"
	cs, err := loadCauses(src)
	if err != nil {
		t.Fatal(err)
	}
	caught := false
	for _, c := range cs {
		if c.Status == "rowed" && strings.HasPrefix(c.FR, "FR-") && !ledgerHasRow(ledger, c.FR) {
			caught = true
		}
	}
	if !caught {
		t.Fatalf("the ledger check did not catch %s", bogus)
	}
}

func TestCausesTableShape(t *testing.T) {
	cs, err := loadCauses(causesTSV)
	if err != nil {
		t.Fatal(err)
	}
	if len(cs) < 30 {
		t.Fatalf("only %d causes — the frontend's refusal vocabulary is larger than that", len(cs))
	}
	// every FR-row id cited by the table that the frontend measures by
	// string must have a pattern (static-only rows are the two whose text
	// is the inner cause's).
	for _, c := range cs {
		if c.Pattern == nil && c.ID != "global-type-unlowerable" {
			t.Errorf("cause %s has no dynamic pattern", c.ID)
		}
	}
	// malformed rows refuse
	for _, bad := range []string{
		"id\tfr\tstatus\tscope\tpattern\tkey\tdiagnosis\nx\tFR-1\trowed\tdecl\t(\t-\td\n",                                // bad regexp
		"id\tfr\tstatus\tscope\tpattern\tkey\tdiagnosis\nx\tnonsense\trowed\tdecl\tp\t-\td\n",                            // bad fr token
		"id\tfr\tstatus\tscope\tpattern\tkey\tdiagnosis\nx\tFR-1\tmaybe\tdecl\tp\t-\td\n",                                // bad status
		"id\tfr\tstatus\tscope\tpattern\tkey\tdiagnosis\nx\tFR-1\trowed\tdecl\tp\t-\td\nx\tFR-2\trowed\tdecl\tq\t-\te\n", // dup id
	} {
		if _, err := loadCauses(bad); err == nil {
			t.Errorf("malformed table accepted: %q", bad)
		}
	}
}

func TestStaticCauseIDsAreRowed(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
}

// TestMachineSurfaceCitesSources — every machine-surface row names a
// frontend source file that exists and mentions the entry's last segment.
func TestMachineSurfaceCitesSources(t *testing.T) {
	s := &supply{sourceThrough: map[string]bool{}, shim: map[string]string{}, intercept: map[string]bool{},
		shadowType: map[string]bool{}, syncType: map[string]bool{}, syncOp: map[string]bool{},
		atomicKind: map[string]bool{}, initCallee: map[string]bool{}}
	if err := readMachineSurface(machineSurfaceTSV, s); err != nil {
		t.Fatal(err)
	}
	for _, line := range strings.Split(machineSurfaceTSV, "\n") {
		if strings.HasPrefix(line, "#") || strings.HasPrefix(line, "kind\t") || strings.TrimSpace(line) == "" {
			continue
		}
		f := strings.Split(line, "\t")
		src := filepath.Join("../..", f[2])
		b, err := os.ReadFile(src)
		if err != nil {
			t.Errorf("row %s cites %s: %v", f[1], f[2], err)
			continue
		}
		seg := f[1]
		if i := strings.LastIndex(seg, "."); i >= 0 {
			seg = seg[i+1:]
		}
		if !strings.Contains(string(b), seg) {
			t.Errorf("row %s: %s does not mention %q", f[1], f[2], seg)
		}
	}
}

func TestRegisterIsRead(t *testing.T) {
	sup, err := newSupply("../../docs/stdlib-admission-register.md")
	if err != nil {
		t.Fatal(err)
	}
	if !sup.sourceThrough["strings"] || sup.shim["fmt.Sprintf"] == "" || !sup.intercept["slices.Sort"] {
		t.Fatalf("register not read: source-through strings=%v shim fmt.Sprintf=%q intercept slices.Sort=%v", sup.sourceThrough["strings"], sup.shim["fmt.Sprintf"], sup.intercept["slices.Sort"])
	}
	if sup.registerRows < 20 {
		t.Fatalf("only %d register rows read", sup.registerRows)
	}
	if _, err := newSupply("/nonexistent/register.md"); err == nil {
		t.Fatal("a missing register must refuse, not default to an empty supply")
	}
}

func TestClassifyTextVocabulary(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	cases := map[string]string{
		`native frontend unsupported: package-selector call time.Date (package "time" surface not modeled)`:                                                       "stdlib-package-unmodeled",
		`method Record.All (instantiation of imported generic type iter.Seq2[cedargo/types.String,cedargo/types.Value]; satisfaction answers, calls fail closed)`: "imported-generic-inst",
		`method cedargo/types.Record.All is unsupported (instantiation of imported generic type iter.Seq2[x]) and its own SIGNATURE does not lower either (…)`:    "imported-generic-sig",
		`range over func(yield func(int) bool)`:                                                                   "range-over-func",
		`anonymous non-empty struct type struct{a int}`:                                                           "anon-struct",
		`builtin println in statement position`:                                                                   "print-builtin",
		`fmt.Println is outside the modeled subset (modeled fmt direct-call members: Errorf, …)`:                  "stdlib-member-unmodeled",
		`fmt.Sprintf verb %x over an argument of type rune is outside the modeled verb/kind matrix (format "%x")`: "fmt-verb-matrix",
		`sync.Map (only Mutex/RWMutex/WaitGroup/Once are modeled)`:                                                "sync-unmodeled",
		`goto function hoists a captured variable x`:                                                              "goto-hoist",
		`goto target label L not at function body top level`:                                                      "goto-nested-label",
		`basic type complex128`:                                                                                   "complex",
		`duplicate TypeId main.T (a function-local type collides with another declaration)`:                       "duplicate-typeid",
		`stdlib source-through: internal/stringslite.Clone needs unsafe.String (…)`:                               "stdlib-source-gap",
		`references quarantined package-level variable maxDatetime (its initializer does not lower: …)`:           "quarantine-cascade",
		`imported package-level variable time.UTC has no seeded cell`:                                             "stdlib-var-unmodeled",
	}
	for text, want := range cases {
		c, _ := classifyText(text)
		got := "UNCLASSIFIED"
		if c != nil {
			got = c.ID
		}
		if got != want {
			t.Errorf("%q -> %s, want %s", text, got, want)
		}
	}
	c, key := classifyText(`native frontend unsupported: package-selector call time.Date (package "time" surface not modeled)`)
	if c == nil || key != "time.Date" {
		t.Errorf("key extraction: got %q", key)
	}
	if c, key := classifyText("something entirely new the table has never seen"); c != nil || key == "" {
		t.Errorf("an unknown text must stay unclassified with its head as key; got %v %q", c, key)
	}
}

func fixtureReport(t *testing.T, dir string) *report {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	sup, err := newSupply("../../docs/stdlib-admission-register.md")
	if err != nil {
		t.Fatal(err)
	}
	prog, err := loadProgram(dir, sup)
	if err != nil {
		t.Fatalf("load %s: %v", dir, err)
	}
	prog.census()
	return buildReport(prog, dir, "test", "test", "docs/stdlib-admission-register.md", "", -1, "")
}

// TestFixtureFiveBlockers — testdata/fivecauses has exactly five known
// blockers (one declaration each); the report must find exactly those.
func TestFixtureFiveBlockers(t *testing.T) {
	r := fixtureReport(t, "testdata/fivecauses")
	want := map[string]bool{"range-over-func": true, "anon-struct": true, "complex": true, "stdlib-package-unmodeled": true, "init-callee-unmodeled": true}
	got := map[string]bool{}
	for _, c := range r.Causes {
		got[c.Cause] = true
	}
	for id := range want {
		if !got[id] {
			t.Errorf("cause %s not reported; got %v", id, keys(got))
		}
	}
	for id := range got {
		if !want[id] {
			t.Errorf("unexpected cause %s reported", id)
		}
	}
	if len(r.Causes) != 5 {
		t.Errorf("want exactly 5 causes, got %d: %v", len(r.Causes), keys(got))
	}
	// the initializer kill is export-scoped and its var is the site
	var kills int
	for _, d := range r.Declarations {
		if d.ExportKill {
			kills++
			if d.Kind != "var" || d.Name != "epoch" {
				t.Errorf("export kill on %s %s, want var epoch", d.Kind, d.Name)
			}
		}
	}
	if kills != 1 {
		t.Errorf("want 1 export-kill declaration, got %d", kills)
	}
	if r.Lowers == 0 || r.Lowers+r.Refused+r.MayRefuse != r.Decls {
		t.Errorf("distance arithmetic: lowers %d refused %d may %d decls %d", r.Lowers, r.Refused, r.MayRefuse, r.Decls)
	}
	// the clean declarations lower
	for _, d := range r.Declarations {
		if strings.HasPrefix(d.Name, "clean") && d.Verdict != "lowers(static)" {
			t.Errorf("%s %s: %s (%v)", d.Kind, d.Name, d.Verdict, d.Causes)
		}
	}
}

func keys(m map[string]bool) []string {
	var out []string
	for k := range m {
		out = append(out, k)
	}
	return out
}

// TestReportIsDeterministic — the same tree renders byte-identical text
// and JSON across runs.
func TestReportIsDeterministic(t *testing.T) {
	var outs [][]byte
	for i := 0; i < 3; i++ {
		r := fixtureReport(t, "testdata/fivecauses")
		var buf bytes.Buffer
		writeHuman(&buf, r)
		if err := writeJSON(&buf, r); err != nil {
			t.Fatal(err)
		}
		writeDeclsTSV(&buf, r)
		writeHistogramTSV(&buf, r)
		outs = append(outs, buf.Bytes())
	}
	for i := 1; i < len(outs); i++ {
		if !bytes.Equal(outs[0], outs[i]) {
			t.Fatalf("run %d differs from run 0", i)
		}
	}
	if !bytes.HasPrefix(outs[0], []byte("DIAGNOSTIC — NOT A LOWERING")) {
		t.Fatalf("the report does not open with the diagnostic banner")
	}
}

// TestFirstRefusalLocatesExportSite — the dynamic pass's text for the
// fixture is FR-14's string, but the static census places the key at an
// export-scoped initializer: the report must say so.
func TestFirstRefusalLocatesExportSite(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	sup, err := newSupply("../../docs/stdlib-admission-register.md")
	if err != nil {
		t.Fatal(err)
	}
	prog, err := loadProgram("testdata/fivecauses", sup)
	if err != nil {
		t.Fatal(err)
	}
	prog.census()
	r := buildReport(prog, "x", "c", "g", "reg", `nativefrontend: native frontend unsupported: package-selector call time.Unix (package "time" surface not modeled)`+"\n", 1, "")
	if r.First == nil || r.First.Cause != "stdlib-package-unmodeled" || r.First.Key != "time.Unix" {
		t.Fatalf("first refusal: %+v", r.First)
	}
	if !strings.Contains(r.First.StaticSite, "EXPORT-scoped") || !regexp.MustCompile(`var epoch`).MatchString(r.First.StaticSite) {
		t.Fatalf("static site did not name the export-scoped initializer: %q", r.First.StaticSite)
	}
	r2 := buildReport(prog, "x", "c", "g", "reg", "", 0, "")
	if !r2.FrontendOK || r2.First != nil {
		t.Fatalf("rc 0 must read as export OK")
	}
}

func TestWireFileNamesRefused(t *testing.T) {
	for _, n := range []string{"x.wire.json", "wire.json", "twin.WIRE.JSON", "x.wire.json.tmp", "Wire.Json.bak", "a_wire.json"} {
		if err := writeFileWith(filepath.Join(t.TempDir(), n), func(*os.File) {}); err == nil {
			t.Errorf("a diagnostic under wire-like name %q must be refused", n)
		}
	}
	if err := writeFileWith(filepath.Join(t.TempDir(), "report.txt"), func(*os.File) {}); err != nil {
		t.Fatal(err)
	}
}

// TestCrashedFrontendIsNotExportOK — audit fix round 1 (HIGH, fail-open):
// a nonzero exit with an empty stderr (a crashed frontend, a shim exit 3)
// must print INFRA naming the rc, never EXPORT OK; only rc 0 is OK; a
// timeout is INFRA; a nonzero rc WITH a named refusal is the first refusal.
func TestCrashedFrontendIsNotExportOK(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	sup, err := newSupply("../../docs/stdlib-admission-register.md")
	if err != nil {
		t.Fatal(err)
	}
	prog, err := loadProgram("testdata/fivecauses", sup)
	if err != nil {
		t.Fatal(err)
	}
	prog.census()
	for _, tc := range []struct {
		rc     int
		stderr string
		ok     bool
		cause  string
	}{
		{3, "", false, "INFRA"},
		{3, "panic: runtime error\n", false, "INFRA"},
		{1, "exit status 1\n", false, "INFRA"},
		{124, "", false, "INFRA"},
		{97, "", false, "INFRA"},
		{0, "", true, ""},
		{0, "# DIAGNOSTIC banner only\n", true, ""},
		{1, "nativefrontend: native frontend unsupported: basic type complex128\n", false, "complex"},
		{1, "# DIAGNOSTIC — NOT A LOWERING\n# frontend exit status: 1\nnativefrontend: native frontend unsupported: basic type complex128\n", false, "complex"},
	} {
		r := buildReport(prog, "x", "c", "g", "reg", tc.stderr, tc.rc, "")
		if r.FrontendOK != tc.ok {
			t.Errorf("rc %d stderr %q: FrontendOK=%v want %v", tc.rc, tc.stderr, r.FrontendOK, tc.ok)
		}
		if tc.cause != "" && (r.First == nil || r.First.Cause != tc.cause) {
			t.Errorf("rc %d stderr %q: first=%+v want cause %s", tc.rc, tc.stderr, r.First, tc.cause)
		}
		if tc.cause == "INFRA" && r.First != nil && !strings.Contains(r.First.Key+r.First.Note, "rc "+itoa(tc.rc)) && tc.rc != 124 {
			t.Errorf("rc %d: INFRA line must name the rc: %+v", tc.rc, r.First)
		}
		var buf bytes.Buffer
		writeHuman(&buf, r)
		if !tc.ok && strings.Contains(buf.String(), "EXPORT OK") {
			t.Errorf("rc %d: the human report says EXPORT OK", tc.rc)
		}
	}
	// a quarantine list on rc 0 is surfaced
	r := buildReport(prog, "x", "c", "g", "reg", "", 0, "# banner\npkg\tkind\tname\tstatus\tcause\tclass\tkey\nmain\tfunc\tf\tquarantined\tbasic type complex128\tFR-15/complex\tcomplex\nmain\tfunc\tgoleanShimX\tquarantined\tx\ty\tz\n")
	if len(r.WireQuarantines) != 1 || !strings.Contains(r.WireQuarantines[0], "func f") {
		t.Fatalf("wire quarantines: %v", r.WireQuarantines)
	}
}

func itoa(i int) string { return fmt.Sprintf("%d", i) }

// ---- machine-surface.tsv vs the frontend's own tables (audit fix round 3) ----

// frontendSurface derives, with go/ast, the modeled sync ops (syncOpFor +
// syncValueOpFor + emitSyncOpStmt's prim/m cases), the sync types (wire.go's
// sync arm + Locker), the atomics prefixes/kinds (atomics.go tables) and
// pureUnmodeledCallees (emit.go) from the frontend sources.
type surfaceSets struct {
	syncTypes, syncOps, atomicPrefixes, atomicKinds, initCallees map[string]bool
}

func frontendSurface(t *testing.T) surfaceSets {
	fset := token.NewFileSet()
	parse := func(name string) *ast.File {
		f, err := parser.ParseFile(fset, filepath.Join("../nativefrontend", name), nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		return f
	}
	emit, atomics, wire := parse("emit.go"), parse("atomics.go"), parse("wire.go")
	ss := surfaceSets{map[string]bool{}, map[string]bool{}, map[string]bool{}, map[string]bool{}, map[string]bool{}}
	strLit := func(e ast.Expr) (string, bool) {
		if bl, ok := e.(*ast.BasicLit); ok && bl.Kind == token.STRING {
			s, err := strconv.Unquote(bl.Value)
			return s, err == nil
		}
		return "", false
	}
	isIdent := func(e ast.Expr, names ...string) bool {
		id, ok := e.(*ast.Ident)
		if !ok {
			return false
		}
		for _, n := range names {
			if id.Name == n {
				return true
			}
		}
		return false
	}
	// sync ops from the three functions
	var funcs = map[string]bool{"syncOpFor": true, "syncValueOpFor": true, "emitSyncOpStmt": true}
	found := 0
	for _, d := range emit.Decls {
		fd, ok := d.(*ast.FuncDecl)
		if !ok || !funcs[fd.Name.Name] || fd.Body == nil {
			continue
		}
		found++
		// prim/method switch shapes
		var walk func(n ast.Node, prim string)
		walk = func(n ast.Node, prim string) {
			ast.Inspect(n, func(m ast.Node) bool {
				switch x := m.(type) {
				case *ast.SwitchStmt:
					if isIdent(x.Tag, "prim") {
						for _, cc := range x.Body.List {
							c := cc.(*ast.CaseClause)
							for _, e := range c.List {
								if p, ok := strLit(e); ok {
									for _, st := range c.Body {
										walk(st, p)
									}
								}
							}
						}
						return false
					}
					if isIdent(x.Tag, "method", "m") && prim != "" {
						for _, cc := range x.Body.List {
							for _, e := range cc.(*ast.CaseClause).List {
								if mth, ok := strLit(e); ok {
									ss.syncOps["sync."+prim+"."+mth] = true
								}
							}
						}
						return false
					}
				case *ast.BinaryExpr:
					// prim == "X" && m == "Y"   |   method == "Y" (prim from the enclosing case)
					if x.Op == token.LAND {
						var p, mth string
						for _, side := range []ast.Expr{x.X, x.Y} {
							if be, ok := side.(*ast.BinaryExpr); ok && be.Op == token.EQL {
								if v, ok := strLit(be.Y); ok {
									if isIdent(be.X, "prim") {
										p = v
									} else if isIdent(be.X, "method", "m") {
										mth = v
									}
								}
							}
						}
						if p != "" && mth != "" {
							ss.syncOps["sync."+p+"."+mth] = true
						}
					}
					if x.Op == token.EQL && prim != "" && isIdent(x.X, "method", "m") {
						if v, ok := strLit(x.Y); ok {
							ss.syncOps["sync."+prim+"."+v] = true
						}
					}
				}
				return true
			})
		}
		walk(fd.Body, "")
	}
	if found != 3 {
		t.Fatalf("expected syncOpFor, syncValueOpFor, emitSyncOpStmt in emit.go; found %d", found)
	}
	// sync types: wire.go's `case "Mutex", "RWMutex", "WaitGroup", "Once":` (the
	// clause whose sibling default refuses "sync.%s (only ...") + Locker.
	ast.Inspect(wire, func(n ast.Node) bool {
		sw, ok := n.(*ast.SwitchStmt)
		if !ok {
			return true
		}
		hasRefusal := false
		for _, cc := range sw.Body.List {
			c := cc.(*ast.CaseClause)
			if c.List == nil {
				ast.Inspect(&ast.BlockStmt{List: c.Body}, func(m ast.Node) bool {
					if bl, ok := m.(*ast.BasicLit); ok && strings.Contains(bl.Value, "sync.%s (only") {
						hasRefusal = true
					}
					return true
				})
			}
		}
		if !hasRefusal {
			return true
		}
		for _, cc := range sw.Body.List {
			for _, e := range cc.(*ast.CaseClause).List {
				if v, ok := strLit(e); ok {
					ss.syncTypes["sync."+v] = true
				}
			}
		}
		return false
	})
	ss.syncTypes["sync.Locker"] = true // `obj.Name() != "Locker"` guard: a plain interface
	// atomics tables and pureUnmodeledCallees
	keysOf := func(f *ast.File, name string, want string) {
		ast.Inspect(f, func(n ast.Node) bool {
			vs, ok := n.(*ast.ValueSpec)
			if !ok || len(vs.Names) != 1 || vs.Names[0].Name != name || len(vs.Values) != 1 {
				return true
			}
			cl, ok := vs.Values[0].(*ast.CompositeLit)
			if !ok {
				return true
			}
			for _, el := range cl.Elts {
				switch x := el.(type) {
				case *ast.KeyValueExpr:
					if v, ok := strLit(x.Key); ok {
						switch want {
						case "kind":
							ss.atomicKinds[v] = true
						case "init":
							ss.initCallees[v] = true
						}
					}
				case *ast.CompositeLit: // {"CompareAndSwap", "cas"}
					if len(x.Elts) == 2 {
						if v, ok := strLit(x.Elts[0]); ok {
							ss.atomicPrefixes[v] = true
						}
					}
				}
			}
			return false
		})
	}
	keysOf(atomics, "atomicIntSuffixes", "kind")
	keysOf(atomics, "atomicOpPrefixes", "prefix")
	keysOf(emit, "pureUnmodeledCallees", "init")
	return ss
}

// checkMachineSurface compares a machine-surface table against the derived
// sets, BOTH ways.
func checkMachineSurface(tsv string, ss surfaceSets) error {
	s := &supply{sourceThrough: map[string]bool{}, shim: map[string]string{}, intercept: map[string]bool{},
		shadowType: map[string]bool{}, syncType: map[string]bool{}, syncOp: map[string]bool{},
		atomicKind: map[string]bool{}, initCallee: map[string]bool{}}
	if err := readMachineSurface(tsv, s); err != nil {
		return err
	}
	prefixes := map[string]bool{}
	for _, p := range s.atomicPrefix {
		prefixes[p] = true
	}
	var errs []string
	cmp := func(what string, table, frontend map[string]bool) {
		for k := range table {
			if !frontend[k] {
				errs = append(errs, what+": table row "+k+" is NOT in the frontend's tables")
			}
		}
		for k := range frontend {
			if !table[k] {
				errs = append(errs, what+": frontend models "+k+" but the table lacks it")
			}
		}
	}
	cmp("sync-type", s.syncType, ss.syncTypes)
	cmp("sync-op", s.syncOp, ss.syncOps)
	cmp("atomic-op-prefix", prefixes, ss.atomicPrefixes)
	cmp("atomic-kind", s.atomicKind, ss.atomicKinds)
	cmp("init-callee", s.initCallee, ss.initCallees)
	if len(errs) > 0 {
		sort.Strings(errs)
		return fmt.Errorf("%s", strings.Join(errs, "\n"))
	}
	return nil
}

func TestMachineSurfaceEqualsFrontendTables(t *testing.T) {
	ss := frontendSurface(t)
	if len(ss.syncOps) < 10 || len(ss.syncTypes) != 5 || len(ss.atomicPrefixes) != 5 || len(ss.atomicKinds) != 5 || len(ss.initCallees) != 2 {
		t.Fatalf("derivation looks wrong: ops=%d types=%d prefixes=%d kinds=%d init=%d", len(ss.syncOps), len(ss.syncTypes), len(ss.atomicPrefixes), len(ss.atomicKinds), len(ss.initCallees))
	}
	if err := checkMachineSurface(machineSurfaceTSV, ss); err != nil {
		t.Fatal(err)
	}
	// red-first: the audit's fabrication (RLocker as a modeled op) is caught,
	// and so is a DROPPED real row.
	fab := machineSurfaceTSV + "sync-op\tsync.RWMutex.RLocker\ttools/nativefrontend/emit.go\tfabricated\n"
	if err := checkMachineSurface(fab, ss); err == nil || !strings.Contains(err.Error(), "RLocker") {
		t.Fatalf("fabricated RLocker row not caught: %v", err)
	}
	dropped := strings.Replace(machineSurfaceTSV, "sync-op\tsync.WaitGroup.Done\t", "#dropped\t", 1)
	if err := checkMachineSurface(dropped, ss); err == nil || !strings.Contains(err.Error(), "WaitGroup.Done") {
		t.Fatalf("dropped Done row not caught: %v", err)
	}
}

// ---- library-refusals.tsv witnesses -----------------------------------------

func TestLibraryRefusalsWitnessed(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	rows, err := loadLibraryRefusals(libraryRefusalsTSV)
	if err != nil {
		t.Fatal(err)
	}
	b, err := os.ReadFile("../../baselines/native-full.tsv")
	if err != nil {
		t.Fatal(err)
	}
	status := map[string]string{}
	for _, l := range strings.Split(string(b), "\n") {
		if strings.HasPrefix(l, "#") {
			continue
		}
		f := strings.Split(l, "\t")
		if len(f) >= 2 {
			status[f[1]] = f[0]
		}
	}
	for _, r := range rows {
		if r.Witness == "-" {
			if !strings.Contains(r.Detail, "register row") && !strings.Contains(r.Detail, "wire") {
				t.Errorf("%s: no witness and the detail cites neither the register nor a wire", r.Member)
			}
			continue
		}
		switch status[r.Witness] {
		case "FAIL":
		case "":
			t.Errorf("%s cites witness %s which is not in the baseline", r.Member, r.Witness)
		default:
			t.Errorf("%s cites witness %s which is %s — the gap closed; the row is STALE", r.Member, r.Witness, status[r.Witness])
		}
	}
}

// ---- vocabulary coverage --------------------------------------------------

// TestVocabularyCoverageIsTracked — the causes table's coverage of the
// frontend's refusal vocabulary is measured, and the unclassified remainder
// is the tracked list (a new unsup(...) string the table does not classify
// shows up here, never silently).
func TestVocabularyCoverageIsTracked(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	total, n, un, err := vocabularyCoverage("../nativefrontend")
	if err != nil {
		t.Fatal(err)
	}
	if total < 300 || n*10 < total*9 {
		t.Fatalf("coverage %d/%d — below the 90%% the design doc states", n, total)
	}
	b, err := os.ReadFile("unclassified-formats.txt")
	if err != nil {
		t.Fatal(err)
	}
	var tracked []string
	for _, l := range strings.Split(string(b), "\n") {
		if strings.HasPrefix(l, "#") || strings.TrimSpace(l) == "" {
			continue
		}
		tracked = append(tracked, l)
	}
	if strings.Join(tracked, "\n") != strings.Join(un, "\n") {
		t.Fatalf("unclassified-formats.txt != the measured unclassified set (regenerate with `lowerdiag vocabulary tools/nativefrontend`):\nwant:\n%s\nhave:\n%s", strings.Join(un, "\n"), strings.Join(tracked, "\n"))
	}
}

// ---- calibration against a real wire (audit fix round 6) -------------------

// TestCalibrationAgainstWire runs the REAL frontend on testdata/calib and
// asserts, per user declaration, that the static verdict equals the wire's
// quarantine set — except declarations the static pass declares NOT judged
// (those referencing fmt shim members), which are reported, not asserted.
func TestCalibrationAgainstWire(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	repo, _ := filepath.Abs("../..")
	fixture := filepath.Join(repo, "tools/lowerdiag/testdata/calib")
	probe := filepath.Join(t.TempDir(), "calib.probe.DIAGNOSTIC-COPY.json")
	cache := os.Getenv("GOCACHE")
	if cache == "" {
		cache = filepath.Join(repo, "artifacts", "go-build-cache")
	}
	cmd := exec.Command("go", "run", "./tools/nativefrontend", "--dir", fixture, "--out", probe)
	cmd.Dir = repo
	cmd.Env = append(os.Environ(), "GO111MODULE=off", "GOCACHE="+cache)
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("the frontend must lower the calibration fixture's export (fail closed — the test cannot run without deps/go at the pin): %v\n%s", err, out)
	}
	wb, err := os.ReadFile(probe)
	if err != nil {
		t.Fatal(err)
	}
	var w map[string]any
	if err := json.Unmarshal(wb, &w); err != nil {
		t.Fatal(err)
	}
	wireQ := map[string]string{}
	for _, f := range asList(w["funcs"]) {
		if u, ok := f["unsupported"].(string); ok {
			wireQ[str(f["name"])] = u
		} else {
			wireQ[str(f["name"])] = ""
		}
	}
	sup, err := newSupply(filepath.Join(repo, "docs/stdlib-admission-register.md"))
	if err != nil {
		t.Fatal(err)
	}
	prog, err := loadProgram(fixture, sup)
	if err != nil {
		t.Fatal(err)
	}
	prog.census()
	checked, disagreements := 0, []string{}
	for _, d := range prog.pkgs["main"].decls {
		if d.Kind != "func" || d.IsGeneric {
			continue
		}
		u, inWire := wireQ[d.Name]
		if !inWire {
			t.Errorf("static decl %s not in the wire", d.Name)
			continue
		}
		unjudged := false
		for _, s := range d.Supplied {
			if strings.Contains(s, "(shim)") {
				unjudged = true
			}
		}
		if unjudged {
			t.Logf("not judged (shim member): %s — wire: %q", d.Name, u)
			continue
		}
		checked++
		staticRefused := len(d.declRefusals()) > 0
		if staticRefused != (u != "") {
			disagreements = append(disagreements, fmt.Sprintf("%s: static refused=%v (%v) wire=%q", d.Name, staticRefused, d.Findings, u))
		}
	}
	if checked < 8 {
		t.Fatalf("only %d declarations checked", checked)
	}
	if len(disagreements) > 0 {
		t.Fatalf("static verdict != wire on %d declaration(s):\n%s", len(disagreements), strings.Join(disagreements, "\n"))
	}
	// the specific shapes the round was about
	// isE LOWERS in the wire: the quarantine sits on the library function
	// (errors.Is itself), so the static finding is CALL-scoped and the
	// declaration agrees with the wire.
	want := map[string]bool{"retBox": false, "assignBox": true, "sortStrings": true, "sortInts": false, "deferSort": true, "isE": false, "fields": false}
	if wireQ["errors.Is"] == "" {
		t.Errorf("wire: the library function errors.Is should be quarantined (library-refusals.tsv row); got lowered")
	}
	for name, refused := range want {
		if (wireQ[name] != "") != refused {
			t.Errorf("wire: %s quarantined=%v want %v (%q)", name, wireQ[name] != "", refused, wireQ[name])
		}
	}
}
