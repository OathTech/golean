package main

// report.go — aggregation over the per-declaration census and the two
// renderings (human text, JSON). Everything is sorted; nothing here reads
// the clock, so a report is byte-identical across runs at one tree.

import (
	"encoding/json"
	"fmt"
	"io"
	"sort"
	"strings"
)

const diagnosticBanner = "DIAGNOSTIC — NOT A LOWERING. tools/lowerdiag report: no wire is written; nothing in this file is a gate input."

type causeRow struct {
	Cause     string   `json:"cause"`
	FR        string   `json:"fr"`
	Status    string   `json:"status"`
	Scope     string   `json:"scope"`
	Decls     int      `json:"decls"`
	Sole      int      `json:"sole"`
	Packages  int      `json:"packages"`
	ExportOf  int      `json:"export_kills"` // declarations where this cause is export-scoped
	TopKeys   []string `json:"top_keys"`
	Diagnosis string   `json:"diagnosis"`
}

type keyRow struct {
	Key      string `json:"key"`
	Cause    string `json:"cause"`
	FR       string `json:"fr"`
	Decls    int    `json:"decls"`
	Sole     int    `json:"sole"`
	Packages int    `json:"packages"`
}

type pkgRow struct {
	Package      string `json:"package"`
	Decls        int    `json:"decls"`
	Funcs        int    `json:"funcs_methods"`
	Lowers       int    `json:"lowers_static"`
	FuncsLower   int    `json:"funcs_methods_lower_static"`
	MayRefuse    int    `json:"may_refuse"`
	Refused      int    `json:"refused_static"`
	ExportStatus string `json:"export_status"` // ok | killed (own: …) | killed (inherited from …)
	AfterTop     int    `json:"lowers_after_top_fixes"`
}

type projectionStep struct {
	Fixed          []string `json:"fixed_causes"`
	DeclsLower     int      `json:"decls_lowering"`
	Gain           int      `json:"gain"`
	ExportsRevived int      `json:"exports_revived"`
}

type declOut struct {
	Pkg           string   `json:"pkg"`
	Kind          string   `json:"kind"`
	Name          string   `json:"name"`
	Pos           string   `json:"pos"`
	LOC           int      `json:"loc"`
	Verdict       string   `json:"verdict"`
	ExportKill    bool     `json:"export_kill"`
	Causes        []string `json:"causes"` // "cause:key[@pos][ (may)][ EXPORT]"
	Supplied      []string `json:"supplied"`
	ImportedTypes []string `json:"imported_types"`
}

type firstRefusal struct {
	Text       string `json:"text"`
	Cause      string `json:"cause"`
	FR         string `json:"fr"`
	Key        string `json:"key"`
	Scope      string `json:"scope"`
	StaticSite string `json:"static_site"`
	Note       string `json:"note"`
}

type report struct {
	Banner         string           `json:"banner"`
	Target         string           `json:"target"`
	Commit         string           `json:"commit"`
	GoVersion      string           `json:"go_version"`
	Register       string           `json:"register"`
	RegisterRows   int              `json:"register_rows"`
	CausesRows     int              `json:"causes_rows"`
	First          *firstRefusal    `json:"first_refusal"`
	FrontendOK     bool             `json:"frontend_export_ok"`
	Decls          int              `json:"decls"`
	Funcs          int              `json:"funcs_methods"`
	Lowers         int              `json:"decls_lowering_static"`
	FuncsLower     int              `json:"funcs_methods_lowering_static"`
	MayRefuse      int              `json:"decls_may_refuse"`
	Refused        int              `json:"decls_refused_static"`
	ExportKills    int              `json:"export_kill_decls"`
	KilledPackages int              `json:"packages_export_killed"`
	Packages       []pkgRow         `json:"packages"`
	Causes         []causeRow       `json:"causes"`
	Keys           []keyRow         `json:"stdlib_keys"`
	Projection     []projectionStep `json:"projection"`
	Unrowed        []string         `json:"unrowed_causes_seen"`
	Notes          []string         `json:"notes"`
	Declarations   []declOut        `json:"declarations"`
}

func buildReport(p *program, target, commit, goVersion, registerPath string, frontendStderr string, frontendRan bool) *report {
	r := &report{Banner: diagnosticBanner, Target: target, Commit: commit, GoVersion: goVersion,
		Register: registerPath, RegisterRows: p.sup.registerRows, CausesRows: len(causeList)}
	// Flatten declarations in package order, decl order.
	var all []*declReport
	for _, path := range p.order {
		all = append(all, p.pkgs[path].decls...)
	}
	isFunc := func(d *declReport) bool { return d.Kind == "func" || d.Kind == "method" }
	// Export kills and inheritance over the local import graph.
	killedOwn := map[string][]string{} // pkg -> reasons
	for _, d := range all {
		if d.exportKill() {
			for _, f := range d.Findings {
				if f.Certain && f.Export {
					killedOwn[d.Pkg] = append(killedOwn[d.Pkg], d.Kind+" "+d.Name+": "+f.Cause.ID+" "+f.Key)
				}
			}
		}
	}
	killedBy := map[string]string{} // pkg -> "own" | inherited-from pkg
	var mark func(path string, visiting map[string]bool) string
	mark = func(path string, visiting map[string]bool) string {
		if v, ok := killedBy[path]; ok {
			return v
		}
		if _, own := killedOwn[path]; own {
			killedBy[path] = "own"
			return "own"
		}
		visiting[path] = true
		res := ""
		for _, ip := range p.pkgs[path].imports {
			if visiting[ip] {
				continue
			}
			if v := mark(ip, visiting); v != "" {
				if v == "own" {
					res = ip
				} else {
					res = v
				}
				break
			}
		}
		delete(visiting, path)
		killedBy[path] = res
		return res
	}
	for _, path := range p.order {
		mark(path, map[string]bool{})
	}
	// Per-cause / per-key aggregation over CERTAIN findings.
	type agg struct {
		decls, sole, export int
		pkgs                map[string]bool
		keys                map[string]int
	}
	causes := map[string]*agg{}
	keys := map[string]*agg{}
	keyCause := map[string]*cause{}
	for _, d := range all {
		cf := d.certainFindings()
		ids := map[string]bool{}
		for _, f := range cf {
			ids[f.Cause.ID] = true
		}
		for id := range ids {
			a := causes[id]
			if a == nil {
				a = &agg{pkgs: map[string]bool{}, keys: map[string]int{}}
				causes[id] = a
			}
			a.decls++
			a.pkgs[d.Pkg] = true
			if len(ids) == 1 {
				a.sole++
			}
		}
		seenKey := map[string]bool{}
		for _, f := range cf {
			a := causes[f.Cause.ID]
			a.keys[f.Key]++
			if f.Export {
				a.export++
			}
			if strings.HasPrefix(f.Cause.ID, "stdlib-") || strings.HasPrefix(f.Cause.ID, "sync-") || f.Cause.ID == "atomic-unmodeled" ||
				f.Cause.ID == "imported-generic-inst" || f.Cause.ID == "imported-generic-sig" || f.Cause.ID == "fmt-verb-matrix" ||
				f.Cause.ID == "unsafe" || f.Cause.ID == "reflect" || f.Cause.ID == "init-callee-unmodeled" {
				if seenKey[f.Key] {
					continue
				}
				seenKey[f.Key] = true
				k := keys[f.Key]
				if k == nil {
					k = &agg{pkgs: map[string]bool{}, keys: map[string]int{}}
					keys[f.Key] = k
					keyCause[f.Key] = f.Cause
				}
				k.decls++
				k.pkgs[d.Pkg] = true
				if len(cf) == 1 || allSameKey(cf, f.Key) {
					k.sole++
				}
			}
		}
	}
	// Totals.
	for _, d := range all {
		r.Decls++
		if isFunc(d) {
			r.Funcs++
		}
		switch d.verdict() {
		case "lowers(static)":
			r.Lowers++
			if isFunc(d) {
				r.FuncsLower++
			}
		case "may-refuse(static)":
			r.MayRefuse++
		default:
			r.Refused++
		}
		if d.exportKill() {
			r.ExportKills++
		}
	}
	for _, path := range p.order {
		if killedBy[path] != "" {
			r.KilledPackages++
		}
	}
	// Cause rows, sorted by unblock value: sole desc, decls desc, id.
	for id, a := range causes {
		c := causesByID[id]
		row := causeRow{Cause: id, FR: c.FR, Status: c.Status, Scope: c.Scope, Decls: a.decls, Sole: a.sole,
			Packages: len(a.pkgs), ExportOf: a.export, Diagnosis: c.Diagnosis}
		type kc struct {
			k string
			n int
		}
		var kcs []kc
		for k, n := range a.keys {
			kcs = append(kcs, kc{k, n})
		}
		sort.Slice(kcs, func(i, j int) bool {
			if kcs[i].n != kcs[j].n {
				return kcs[i].n > kcs[j].n
			}
			return kcs[i].k < kcs[j].k
		})
		for i, x := range kcs {
			if i >= 5 {
				break
			}
			row.TopKeys = append(row.TopKeys, fmt.Sprintf("%s×%d", x.k, x.n))
		}
		r.Causes = append(r.Causes, row)
		if c.FR == "unrowed" {
			r.Unrowed = append(r.Unrowed, id)
		}
	}
	sort.Slice(r.Causes, func(i, j int) bool {
		a, b := r.Causes[i], r.Causes[j]
		if a.Sole != b.Sole {
			return a.Sole > b.Sole
		}
		if a.Decls != b.Decls {
			return a.Decls > b.Decls
		}
		return a.Cause < b.Cause
	})
	sort.Strings(r.Unrowed)
	for k, a := range keys {
		r.Keys = append(r.Keys, keyRow{Key: k, Cause: keyCause[k].ID, FR: keyCause[k].FR, Decls: a.decls, Sole: a.sole, Packages: len(a.pkgs)})
	}
	sort.Slice(r.Keys, func(i, j int) bool {
		a, b := r.Keys[i], r.Keys[j]
		if a.Decls != b.Decls {
			return a.Decls > b.Decls
		}
		if a.Sole != b.Sole {
			return a.Sole > b.Sole
		}
		return a.Key < b.Key
	})
	// Projection: fix the top causes cumulatively (by the cause ranking);
	// a declaration lowers once ALL its certain causes are fixed.
	lowersUnder := func(fixed map[string]bool, d *declReport) bool {
		for _, f := range d.certainFindings() {
			if !fixed[f.Cause.ID] {
				return false
			}
		}
		return true
	}
	fixed := map[string]bool{}
	var fixedList []string
	base := 0
	for _, d := range all {
		if lowersUnder(fixed, d) {
			base++
		}
	}
	prev := base
	for i, row := range r.Causes {
		if i >= 8 {
			break
		}
		fixed[row.Cause] = true
		fixedList = append(fixedList, row.Cause)
		n, revived := 0, 0
		for _, d := range all {
			if lowersUnder(fixed, d) {
				n++
			}
		}
		for path := range killedOwn {
			stillKilled := false
			for _, d := range p.pkgs[path].decls {
				for _, f := range d.certainFindings() {
					if f.Export && !fixed[f.Cause.ID] {
						stillKilled = true
					}
				}
			}
			if !stillKilled {
				revived++
			}
		}
		r.Projection = append(r.Projection, projectionStep{Fixed: append([]string(nil), fixedList...), DeclsLower: n, Gain: n - prev, ExportsRevived: revived})
		prev = n
	}
	// Per package (top-3 causes fixed for the "+after" column).
	top3 := map[string]bool{}
	for i, row := range r.Causes {
		if i >= 3 {
			break
		}
		top3[row.Cause] = true
	}
	for _, path := range p.order {
		lp := p.pkgs[path]
		row := pkgRow{Package: path}
		for _, d := range lp.decls {
			row.Decls++
			if isFunc(d) {
				row.Funcs++
			}
			switch d.verdict() {
			case "lowers(static)":
				row.Lowers++
				if isFunc(d) {
					row.FuncsLower++
				}
			case "may-refuse(static)":
				row.MayRefuse++
			default:
				row.Refused++
			}
			if lowersUnder(top3, d) {
				row.AfterTop++
			}
		}
		switch kb := killedBy[path]; kb {
		case "":
			row.ExportStatus = "ok"
		case "own":
			reasons := killedOwn[path]
			sort.Strings(reasons)
			row.ExportStatus = "KILLED (own: " + strings.Join(reasons, "; ") + ")"
		default:
			row.ExportStatus = "KILLED (inherited from " + kb + ")"
		}
		r.Packages = append(r.Packages, row)
	}
	// Declarations (full list, for --json and the TSV).
	for _, d := range all {
		o := declOut{Pkg: d.Pkg, Kind: d.Kind, Name: d.Name, Pos: d.Pos, LOC: d.LOC, Verdict: d.verdict(), ExportKill: d.exportKill(),
			Supplied: append([]string(nil), d.Supplied...), ImportedTypes: append([]string(nil), d.ImportedTypes...)}
		sort.Strings(o.Supplied)
		sort.Strings(o.ImportedTypes)
		for _, f := range d.Findings {
			s := f.Cause.ID + ":" + f.Key + "@" + f.Pos
			if !f.Certain {
				s += " (may)"
			}
			if f.Export {
				s += " EXPORT"
			}
			o.Causes = append(o.Causes, s)
		}
		sort.Strings(o.Causes)
		r.Declarations = append(r.Declarations, o)
	}
	// The first refusal (dynamic pass).
	if frontendRan {
		first := strings.TrimSpace(firstLine(frontendStderr))
		if first == "" {
			r.FrontendOK = true
		} else {
			fr := &firstRefusal{Text: first}
			c, key := classifyText(first)
			if c == nil {
				fr.Cause, fr.FR, fr.Key, fr.Scope = "UNCLASSIFIED", "-", key, "-"
				fr.Note = "the text matched no causes.tsv pattern — add a row (never absorb)"
			} else {
				fr.Cause, fr.FR, fr.Key, fr.Scope = c.ID, c.FR, key, c.Scope
			}
			// Locate the key in the static census: an export-scoped site
			// names the real kill (a body call and an initializer call
			// share one refusal string).
			var sites []string
			for _, d := range all {
				for _, f := range d.Findings {
					sameCause := fr.Cause != "UNCLASSIFIED" && f.Cause.ID == fr.Cause
					if f.Key == key || (sameCause && key == fr.Cause) || (sameCause && strings.HasSuffix(key, "."+f.Key)) || (sameCause && strings.HasSuffix(f.Key, "."+key)) {
						s := d.Pkg + " " + d.Kind + " " + d.Name + " @" + f.Pos + " [" + f.Cause.ID + "/" + f.Cause.FR
						if f.Export {
							s += ", EXPORT-scoped"
						}
						s += "]"
						sites = append(sites, s)
					}
				}
			}
			sort.Strings(sites)
			if len(sites) > 0 {
				fr.StaticSite = strings.Join(dedup(sites), " | ")
				for _, s := range sites {
					if strings.Contains(s, "EXPORT-scoped") {
						fr.Note = "the same refusal string covers a body call and a package-level initializer; the static census places this key at an export-scoped site — that is the kill (see the site's FR row)"
						break
					}
				}
			} else if c != nil {
				fr.Note = "the static census has no declaration with this key: the refusal is at a site the static pass does not model (library text, emitter-table detail such as fmt's verb matrix, or a load-time shape)"
				if isTypeShapedCause(c.ID) && !strings.Contains(key, "(") {
					fr.Note += " — a bare TYPE key with no user declaration carrying it is FR-24's shape: a package-level VARIABLE of a reached source-through library unit whose type does not lower kills the whole export at collectGlobals (cedar-go: encoding/binary.Write -> structSize sync.Map; the refusal text does not name the variable — a message gap recorded in docs/2026-09-04_lower-diagnose.md); cause global-type-unlowerable, " + causesByID["global-type-unlowerable"].Status
				}
			}
			r.First = fr
		}
	}
	r.Notes = []string{
		"static = go/types over the program + its local imports; stdlib judged by the register (source-through members counted as lowering — FR-21 gaps inside library text are invisible here) and the machine-owned surface table",
		"may-refuse = shape-dependent (goto hoisting shapes, non-reserved build tags); the distance line counts only certain refusals",
		"export scope = the frontend refuses the WHOLE package export today (H-11 initializer kill, an init() body, unstubbable method signature, global type, duplicate local TypeId); dependents inherit through the import graph",
		"main.main is not a census declaration: the frontend never emits it (emit.go emitProgram; drivers run named entry functions), so its body cannot block a lowering",
		"not visible statically: fmt's verb×kind matrix, mono.go's stencil-time refusals, per-call-site frontend invariants — the dynamic pass (first refusal) is the check",
	}
	return r
}

// isTypeShapedCause: causes whose refusal text names a TYPE (the FR-24
// heuristic in the first-refusal note).
func isTypeShapedCause(id string) bool {
	switch id {
	case "sync-unmodeled", "sync-cond", "atomic-unmodeled", "anon-struct", "complex", "imported-generic-inst":
		return true
	}
	return false
}

func allSameKey(fs []finding, key string) bool {
	for _, f := range fs {
		if f.Key != key {
			return false
		}
	}
	return true
}

func dedup(xs []string) []string {
	var out []string
	for i, x := range xs {
		if i == 0 || x != xs[i-1] {
			out = append(out, x)
		}
	}
	return out
}

func firstLine(s string) string {
	for _, l := range strings.Split(s, "\n") {
		if strings.TrimSpace(l) != "" {
			return l
		}
	}
	return ""
}

func pct(a, b int) string {
	if b == 0 {
		return "n/a"
	}
	return fmt.Sprintf("%.1f%%", 100*float64(a)/float64(b))
}

// writeHuman renders the report for a reader.
func writeHuman(w io.Writer, r *report) {
	fmt.Fprintln(w, r.Banner)
	fmt.Fprintf(w, "target: %s\ncommit: %s   go: %s\nregister: %s (%d rows)   causes table: %d rows\n\n", r.Target, r.Commit, r.GoVersion, r.Register, r.RegisterRows, r.CausesRows)
	fmt.Fprintln(w, "== first refusal (what the frontend says today)")
	switch {
	case r.First == nil && r.FrontendOK:
		fmt.Fprintln(w, "  frontend: EXPORT OK — the program lowers (per-declaration quarantines, if any, are in the wire's unsupported stubs; the static census below is the demand view)")
	case r.First == nil:
		fmt.Fprintln(w, "  (dynamic pass not run — pass --frontend-stderr)")
	default:
		fmt.Fprintf(w, "  %s\n  -> cause %s [%s, %s-scoped] key %s\n", r.First.Text, r.First.Cause, r.First.FR, r.First.Scope, r.First.Key)
		if r.First.StaticSite != "" {
			fmt.Fprintf(w, "  static site(s): %s\n", r.First.StaticSite)
		}
		if r.First.Note != "" {
			fmt.Fprintf(w, "  note: %s\n", r.First.Note)
		}
	}
	fmt.Fprintln(w, "\n== distance")
	fmt.Fprintf(w, "  declarations demanding nothing refused: %d / %d (%s)   funcs+methods: %d / %d (%s)   may-refuse: %d   refused: %d\n",
		r.Lowers, r.Decls, pct(r.Lowers, r.Decls), r.FuncsLower, r.Funcs, pct(r.FuncsLower, r.Funcs), r.MayRefuse, r.Refused)
	fmt.Fprintf(w, "  export kills: %d declaration(s) refuse the WHOLE export of their package today; %d / %d package(s) export-killed (own or inherited)\n", r.ExportKills, r.KilledPackages, len(r.Packages))
	fmt.Fprintln(w, "\n== blockers by cause (sorted by unblock value: sole = declarations this cause alone blocks)")
	fmt.Fprintf(w, "  %-26s %-16s %-6s %5s %5s %4s %6s  %s\n", "cause", "fr", "scope", "decls", "sole", "pkgs", "export", "top keys")
	for _, c := range r.Causes {
		fr := c.FR
		if c.Status != "rowed" {
			fr += " (" + c.Status + ")"
		}
		fmt.Fprintf(w, "  %-26s %-16s %-6s %5d %5d %4d %6d  %s\n", c.Cause, fr, c.Scope, c.Decls, c.Sole, c.Packages, c.ExportOf, strings.Join(c.TopKeys, ", "))
	}
	if len(r.Causes) == 0 {
		fmt.Fprintln(w, "  (none — every declaration demands nothing the static pass knows to be refused)")
	}
	fmt.Fprintln(w, "\n== top blockers — what each is and where its plan lives")
	for i, c := range r.Causes {
		if i >= 10 {
			break
		}
		fmt.Fprintf(w, "  %2d. %s [%s] — %d decls (%d sole, %d pkgs): %s\n", i+1, c.Cause, c.FR, c.Decls, c.Sole, c.Packages, c.Diagnosis)
	}
	fmt.Fprintln(w, "\n== projection — declarations lowering if the top causes were fixed, cumulatively")
	for _, s := range r.Projection {
		fmt.Fprintf(w, "  + %-26s -> %d / %d lower (+%d), %d export(s) revived\n", s.Fixed[len(s.Fixed)-1], s.DeclsLower, r.Decls, s.Gain, s.ExportsRevived)
	}
	fmt.Fprintln(w, "\n== per package")
	fmt.Fprintf(w, "  %-40s %5s %6s %8s %5s %7s %8s  %s\n", "package", "decls", "lowers", "may-ref", "refd", "+top3", "share", "export")
	for _, pr := range r.Packages {
		fmt.Fprintf(w, "  %-40s %5d %6d %8d %5d %7d %8s  %s\n", pr.Package, pr.Decls, pr.Lowers, pr.MayRefuse, pr.Refused, pr.AfterTop, pct(pr.Lowers, pr.Decls), pr.ExportStatus)
	}
	if len(r.Keys) > 0 {
		fmt.Fprintln(w, "\n== stdlib / imported keys refused (register class = none; top 25)")
		fmt.Fprintf(w, "  %-52s %-26s %-8s %5s %5s %4s\n", "key", "cause", "fr", "decls", "sole", "pkgs")
		for i, k := range r.Keys {
			if i >= 25 {
				break
			}
			fmt.Fprintf(w, "  %-52s %-26s %-8s %5d %5d %4d\n", k.Key, k.Cause, k.FR, k.Decls, k.Sole, k.Packages)
		}
	}
	if len(r.Unrowed) > 0 {
		fmt.Fprintf(w, "\n== UNROWED causes seen (the ledger has no row — direction 3 owes one): %s\n", strings.Join(r.Unrowed, ", "))
	}
	fmt.Fprintln(w, "\n== notes")
	for _, n := range r.Notes {
		fmt.Fprintf(w, "  - %s\n", n)
	}
}

func writeJSON(w io.Writer, r *report) error {
	enc := json.NewEncoder(w)
	enc.SetIndent("", " ")
	return enc.Encode(r)
}

// writeDeclsTSV: the per-declaration table (the census's demand.tsv).
func writeDeclsTSV(w io.Writer, r *report) {
	fmt.Fprintln(w, "# "+diagnosticBanner)
	fmt.Fprintln(w, "pkg\tkind\tname\tpos\tloc\tverdict\texport_kill\tcauses\tsupplied\timported_types")
	for _, d := range r.Declarations {
		fmt.Fprintf(w, "%s\t%s\t%s\t%s\t%d\t%s\t%v\t%s\t%s\t%s\n", d.Pkg, d.Kind, d.Name, d.Pos, d.LOC, d.Verdict, d.ExportKill,
			dash(strings.Join(d.Causes, ",")), dash(strings.Join(d.Supplied, ",")), dash(strings.Join(d.ImportedTypes, ",")))
	}
}

// writeHistogramTSV: per cause and per key (the census's demand-histogram.tsv).
func writeHistogramTSV(w io.Writer, r *report) {
	fmt.Fprintln(w, "# "+diagnosticBanner)
	fmt.Fprintln(w, "kind\tkey\tcause\tfr\tscope\tdecls\tsole\tpackages\texport_kills")
	for _, c := range r.Causes {
		fmt.Fprintf(w, "cause\t%s\t%s\t%s\t%s\t%d\t%d\t%d\t%d\n", c.Cause, c.Cause, c.FR, c.Scope, c.Decls, c.Sole, c.Packages, c.ExportOf)
	}
	for _, k := range r.Keys {
		fmt.Fprintf(w, "key\t%s\t%s\t%s\t-\t%d\t%d\t%d\t-\n", k.Key, k.Cause, k.FR, k.Decls, k.Sole, k.Packages)
	}
}

func writePerPackageTSV(w io.Writer, r *report) {
	fmt.Fprintln(w, "# "+diagnosticBanner)
	fmt.Fprintln(w, "package\tdecls\tfuncs_methods\tlowers_static\tfuncs_methods_lower_static\tmay_refuse\trefused_static\tshare_lowers\tlowers_after_top3\texport_status")
	for _, p := range r.Packages {
		fmt.Fprintf(w, "%s\t%d\t%d\t%d\t%d\t%d\t%d\t%s\t%d\t%s\n", p.Package, p.Decls, p.Funcs, p.Lowers, p.FuncsLower, p.MayRefuse, p.Refused, pct(p.Lowers, p.Decls), p.AfterTop, p.ExportStatus)
	}
}

func dash(s string) string {
	if s == "" {
		return "-"
	}
	return s
}
