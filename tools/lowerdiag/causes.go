package main

// causes.go — the cause table (causes.tsv, embedded) and the two supply
// tables the static pass judges against: the stdlib admission register
// (docs/stdlib-admission-register.md, read at run time — never hardcoded)
// and the machine-owned surface (machine-surface.tsv, embedded, every row
// citing the frontend source it transcribes).

import (
	"bufio"
	_ "embed"
	"fmt"
	"os"
	"regexp"
	"strings"
)

//go:embed causes.tsv
var causesTSV string

//go:embed machine-surface.tsv
var machineSurfaceTSV string

// cause is one row of causes.tsv.
type cause struct {
	ID        string
	FR        string // FR-n | Q-* | out-of-language | by-design | cascade | c-pin | unrowed
	Status    string // rowed | pending:<branch>
	Scope     string // decl | export
	Pattern   *regexp.Regexp
	KeyTmpl   string // "-" = the cause id
	Diagnosis string
}

// frTokens: the non-FR/non-Q values the `fr` column may take.
var frTokens = map[string]bool{
	"out-of-language": true, "by-design": true, "cascade": true, "c-pin": true, "unrowed": true,
}

var causesByID = map[string]*cause{}
var causeList []*cause

func loadCauses(src string) ([]*cause, error) {
	var out []*cause
	seen := map[string]bool{}
	sc := bufio.NewScanner(strings.NewReader(src))
	header := false
	line := 0
	for sc.Scan() {
		line++
		t := sc.Text()
		if strings.HasPrefix(t, "#") || strings.TrimSpace(t) == "" {
			continue
		}
		f := strings.Split(t, "\t")
		if !header {
			if strings.Join(f, "\t") != "id\tfr\tstatus\tscope\tpattern\tkey\tdiagnosis" {
				return nil, fmt.Errorf("causes.tsv line %d: header is %q, want id/fr/status/scope/pattern/key/diagnosis", line, t)
			}
			header = true
			continue
		}
		if len(f) != 7 {
			return nil, fmt.Errorf("causes.tsv line %d: %d columns, want 7", line, len(f))
		}
		c := &cause{ID: f[0], FR: f[1], Status: f[2], Scope: f[3], KeyTmpl: f[5], Diagnosis: f[6]}
		for i, v := range f {
			if strings.TrimSpace(v) == "" {
				return nil, fmt.Errorf("causes.tsv line %d (%s): column %d is empty", line, c.ID, i+1)
			}
		}
		if seen[c.ID] {
			return nil, fmt.Errorf("causes.tsv line %d: duplicate id %s", line, c.ID)
		}
		seen[c.ID] = true
		if !(strings.HasPrefix(c.FR, "FR-") || strings.HasPrefix(c.FR, "Q-") || frTokens[c.FR]) {
			return nil, fmt.Errorf("causes.tsv line %d (%s): fr %q is not FR-n, Q-*, or one of the fixed tokens", line, c.ID, c.FR)
		}
		if c.Status != "rowed" && !strings.HasPrefix(c.Status, "pending:") {
			return nil, fmt.Errorf("causes.tsv line %d (%s): status %q is not rowed|pending:<branch>", line, c.ID, c.Status)
		}
		if c.Scope != "decl" && c.Scope != "export" {
			return nil, fmt.Errorf("causes.tsv line %d (%s): scope %q is not decl|export", line, c.ID, c.Scope)
		}
		if f[4] != "-" {
			re, err := regexp.Compile(f[4])
			if err != nil {
				return nil, fmt.Errorf("causes.tsv line %d (%s): pattern does not compile: %v", line, c.ID, err)
			}
			c.Pattern = re
		}
		out = append(out, c)
	}
	if err := sc.Err(); err != nil {
		return nil, err
	}
	if !header {
		return nil, fmt.Errorf("causes.tsv: no header row")
	}
	return out, nil
}

func initCauses() error {
	cs, err := loadCauses(causesTSV)
	if err != nil {
		return err
	}
	causeList = cs
	for _, c := range cs {
		causesByID[c.ID] = c
	}
	// Every cause id the static pass emits must be a table row (the
	// table is the single vocabulary; a Go-side id with no row would be
	// an uncounted, undiagnosed refusal).
	for _, id := range staticCauseIDs {
		if causesByID[id] == nil {
			return fmt.Errorf("static pass emits cause %q which causes.tsv does not row", id)
		}
	}
	return nil
}

func mustCause(id string) *cause {
	c := causesByID[id]
	if c == nil {
		panic("lowerdiag: unknown cause id " + id + " (initCauses checks staticCauseIDs — add the id there)")
	}
	return c
}

// staticCauseIDs: every cause id static.go can emit (checked against the
// table at start-up, and by TestStaticCauseIDsAreRowed).
var staticCauseIDs = []string{
	"range-over-func", "anon-struct", "goto-hoist", "goto-nested-label", "complex",
	"imported-generic-sig", "imported-generic-inst", "init-callee-unmodeled",
	"global-type-unlowerable", "stdlib-package-unmodeled", "stdlib-member-unmodeled",
	"stdlib-var-unmodeled", "stdlib-value-position", "stdlib-type-method",
	"sync-unmodeled", "sync-cond", "atomic-unmodeled", "unsafe", "reflect", "print-builtin",
	"go-of-builtin", "recv-short-circuit", "method-expr-deref", "range-assign-nonident",
	"tuple-iface-box", "defer-of-builtin", "self-shadow-define", "alloc-short-circuit",
	"duplicate-typeid", "local-import-shape", "build-constraint", "fmt-verb-matrix",
}

// methodWrap unwraps the per-declaration quarantine's "method T.M (cause;
// satisfaction answers, calls fail closed)" wrapper.
var methodWrap = regexp.MustCompile(`^method \S+ \((.*)\)$`)

const refusalPrefix = "native frontend unsupported: "

// classifyText maps one refusal text to its cause row and key. The FIRST
// matching row in table order wins (the table is ordered specific-first);
// an unmatched text is returned with nil cause and its head as the key —
// never absorbed into a known class.
func classifyText(text string) (*cause, string) {
	inner := strings.TrimSpace(text)
	inner = strings.TrimPrefix(inner, "nativefrontend: ")
	inner = strings.TrimPrefix(inner, refusalPrefix)
	if m := methodWrap.FindStringSubmatch(inner); m != nil {
		inner = m[1]
	}
	for _, c := range causeList {
		if c.Pattern == nil {
			continue
		}
		if m := c.Pattern.FindStringSubmatchIndex(inner); m != nil {
			key := c.ID
			if c.KeyTmpl != "-" {
				key = string(c.Pattern.ExpandString(nil, c.KeyTmpl, inner, m))
				key = strings.TrimSpace(key)
				// A template whose groups did not participate (the pattern
				// matched through another alternative) renders as if every
				// group were empty ("fmt. @") — fall back to the cause id.
				empty := make([]int, 2*(c.Pattern.NumSubexp()+1))
				for i := range empty {
					empty[i] = -1
				}
				empty[0], empty[1] = 0, 0
				if key == "" || key == strings.TrimSpace(string(c.Pattern.ExpandString(nil, c.KeyTmpl, inner, empty))) {
					key = c.ID
				}
			}
			return c, key
		}
	}
	head := inner
	if i := strings.IndexAny(head, ":("); i > 0 {
		head = head[:i]
	}
	return nil, strings.TrimSpace(firstWords(head, 8))
}

func firstWords(s string, n int) string {
	w := strings.Fields(s)
	if len(w) > n {
		w = w[:n]
	}
	return strings.Join(w, " ")
}

// ---- the supply tables ----------------------------------------------------

// supply is what lowers today: the register's classes plus the machine
// surface. Lookups answer (class, ok).
type supply struct {
	sourceThrough map[string]bool   // package path -> source-through
	shim          map[string]string // "pkg.Member" -> detail (retained shims: fmt.Sprintf, cmp.Compare)
	intercept     map[string]bool   // "pkg.Member" -> intercepted library member (slices.Sort, cmp.Compare)
	shadowType    map[string]bool   // "pkg.Type" -> E5-T shadow model (sync/atomic.Int32 …)
	registerRows  int
	syncType      map[string]bool // "sync.Mutex"
	syncOp        map[string]bool // "sync.Mutex.Lock"
	atomicPrefix  []string
	atomicKind    map[string]bool
	initCallee    map[string]bool // pureUnmodeledCallees
	surfaceRows   int
}

// readRegister parses the machine block of docs/stdlib-admission-register.md
// (between the register:begin/end markers): rows `class<TAB>entry<TAB>detail`.
// Fail closed: a missing file, missing markers, or an unknown class refuses.
func readRegister(path string, s *supply) error {
	b, err := os.ReadFile(path)
	if err != nil {
		return fmt.Errorf("stdlib admission register unreadable (%v) — the supply table is the register, not a hardcoded list; refusing", err)
	}
	txt := string(b)
	i := strings.Index(txt, "<!-- register:begin -->")
	j := strings.Index(txt, "<!-- register:end -->")
	if i < 0 || j < 0 || j < i {
		return fmt.Errorf("%s: register:begin/end markers not found — refusing", path)
	}
	block := txt[i:j]
	known := map[string]bool{"source-through": true, "substitution": true, "overlay": true, "overlay-import": true,
		"intercept": true, "primitive": true, "shim": true, "shadow-type": true}
	rows := 0
	for _, line := range strings.Split(block, "\n") {
		if strings.HasPrefix(line, "<!--") || strings.HasPrefix(line, "```") || strings.TrimSpace(line) == "" {
			continue
		}
		f := strings.SplitN(line, "\t", 3)
		if len(f) < 2 {
			continue
		}
		class, entry := f[0], f[1]
		if class == "class" && entry == "entry" {
			continue // header
		}
		if class == "count" {
			continue
		}
		if !known[class] {
			return fmt.Errorf("%s: register row has unknown class %q (entry %s) — the diagnostic does not know how to judge it; refusing", path, class, entry)
		}
		rows++
		detail := ""
		if len(f) == 3 {
			detail = f[2]
		}
		switch class {
		case "source-through":
			s.sourceThrough[entry] = true
		case "shim":
			s.shim[entry] = detail
		case "intercept":
			s.intercept[entry] = true
		case "shadow-type":
			s.shadowType[entry] = true
		}
	}
	if rows == 0 {
		return fmt.Errorf("%s: the register block has no rows — refusing", path)
	}
	s.registerRows = rows
	return nil
}

func readMachineSurface(src string, s *supply) error {
	sc := bufio.NewScanner(strings.NewReader(src))
	header := false
	for sc.Scan() {
		t := sc.Text()
		if strings.HasPrefix(t, "#") || strings.TrimSpace(t) == "" {
			continue
		}
		f := strings.Split(t, "\t")
		if !header {
			if t != "kind\tentry\tsource\tdetail" {
				return fmt.Errorf("machine-surface.tsv: header is %q", t)
			}
			header = true
			continue
		}
		if len(f) != 4 {
			return fmt.Errorf("machine-surface.tsv: row %q has %d columns, want 4", t, len(f))
		}
		s.surfaceRows++
		switch f[0] {
		case "sync-type":
			s.syncType[f[1]] = true
		case "sync-op":
			s.syncOp[f[1]] = true
		case "atomic-op-prefix":
			s.atomicPrefix = append(s.atomicPrefix, f[1])
		case "atomic-kind":
			s.atomicKind[f[1]] = true
		case "init-callee":
			s.initCallee[f[1]] = true
		default:
			return fmt.Errorf("machine-surface.tsv: unknown kind %q", f[0])
		}
	}
	return sc.Err()
}

func newSupply(registerPath string) (*supply, error) {
	s := &supply{sourceThrough: map[string]bool{}, shim: map[string]string{}, intercept: map[string]bool{},
		shadowType: map[string]bool{}, syncType: map[string]bool{}, syncOp: map[string]bool{},
		atomicKind: map[string]bool{}, initCallee: map[string]bool{}}
	if err := readRegister(registerPath, s); err != nil {
		return nil, err
	}
	if err := readMachineSurface(machineSurfaceTSV, s); err != nil {
		return nil, err
	}
	return s, nil
}

// shimPackages: the packages with at least one retained shim (a member of
// such a package outside the shim list is `stdlib-member-unmodeled`, the
// frontend's emitStdlibShimCall refusal, not the package-selector one).
func (s *supply) shimPackage(pkg string) bool {
	for k := range s.shim {
		if strings.HasPrefix(k, pkg+".") {
			return true
		}
	}
	return false
}

// atomicFuncModeled mirrors atomics.go atomicFuncOp for a package-level
// sync/atomic function name (LoadInt32, AddUint64, …) or a typed wrapper's
// method name (Load, Add, …).
func (s *supply) atomicModeled(name string) bool {
	for _, p := range s.atomicPrefix {
		if name == p {
			return true // wrapper method
		}
		if strings.HasPrefix(name, p) && s.atomicKind[name[len(p):]] {
			return true
		}
	}
	return false
}
