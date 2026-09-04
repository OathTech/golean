package main

import (
	"bytes"
	"os"
	"path/filepath"
	"regexp"
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
	return buildReport(prog, dir, "test", "test", "docs/stdlib-admission-register.md", "", false)
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
	r := buildReport(prog, "x", "c", "g", "reg", `nativefrontend: native frontend unsupported: package-selector call time.Unix (package "time" surface not modeled)`+"\n", true)
	if r.First == nil || r.First.Cause != "stdlib-package-unmodeled" || r.First.Key != "time.Unix" {
		t.Fatalf("first refusal: %+v", r.First)
	}
	if !strings.Contains(r.First.StaticSite, "EXPORT-scoped") || !regexp.MustCompile(`var epoch`).MatchString(r.First.StaticSite) {
		t.Fatalf("static site did not name the export-scoped initializer: %q", r.First.StaticSite)
	}
	r2 := buildReport(prog, "x", "c", "g", "reg", "", true)
	if !r2.FrontendOK || r2.First != nil {
		t.Fatalf("empty stderr must read as export OK")
	}
}

func TestWireFileNamesRefused(t *testing.T) {
	if err := writeFileWith(filepath.Join(t.TempDir(), "x.wire.json"), func(*os.File) {}); err == nil {
		t.Fatal("a diagnostic under a wire file name must be refused")
	}
}
