// Command lowerdiag is LANE TOOLING: the lowering DIAGNOSTIC that reports
// EVERY blocker a Go program would hit in the native frontend, classified
// by cause and FR row — not only the first refusal the frontend prints.
// Runner: scripts/lower-diagnose; design: docs/2026-09-04_lower-diagnose.md.
//
// It is a REPORT, never a lowering: it writes no wire, and every artifact
// it produces starts with a "DIAGNOSTIC — NOT A LOWERING" line. Not a gate,
// not on the trusted surface; stdlib only, GO111MODULE=off.
//
//	lowerdiag report --repo <root> [--frontend-stderr FILE] [--json]
//	                 [--decls-tsv F] [--histogram-tsv F] [--per-package-tsv F] <dir|main.go>
//	    STATIC pass (go/types over the program + its case-local imports, judged
//	    against docs/stdlib-admission-register.md + machine-surface.tsv) and, when
//	    --frontend-stderr is given, the DYNAMIC pass's first refusal classified
//	    by the same causes.tsv; then the full histogram / projection / distance.
//	lowerdiag wire <wire.json>
//	    per-declaration classification of a golean-native-v1 wire's quarantine
//	    stubs (the census's decls.tsv): pkg kind name status cause class key
//	lowerdiag classify
//	    stdin refusal lines -> class TAB key (class = FR/cause-id)
//
// Two [USER] directions this serves (docs/language-coverage-ledger.md §0):
// (3) every detected gap is rowed with a plan; (4) a refusal comes with the
// full picture — every blocker, classified and counted.
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
)

func main() {
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, "lowerdiag:", err)
		os.Exit(1)
	}
}

func run(args []string) error {
	if err := initCauses(); err != nil {
		return err
	}
	if len(args) == 0 {
		return fmt.Errorf("usage: lowerdiag report [flags] <dir|main.go> | wire <wire.json> | classify")
	}
	switch args[0] {
	case "report":
		return runReport(args[1:])
	case "wire":
		if len(args) != 2 {
			return fmt.Errorf("wire needs exactly one <wire.json>")
		}
		return wire(args[1])
	case "classify":
		return classifyStdin()
	}
	return fmt.Errorf("unknown subcommand %q (report|wire|classify)", args[0])
}

func runReport(args []string) error {
	fs := flag.NewFlagSet("report", flag.ContinueOnError)
	repo := fs.String("repo", ".", "repository root (for docs/stdlib-admission-register.md and baselines/go-oracle-pin)")
	stderrFile := fs.String("frontend-stderr", "", "file holding the real frontend's stderr for this target (the DYNAMIC pass's first refusal); empty file = export OK")
	asJSON := fs.Bool("json", false, "write the JSON report to stdout instead of the human one")
	declsTSV := fs.String("decls-tsv", "", "also write the per-declaration TSV here")
	histTSV := fs.String("histogram-tsv", "", "also write the cause/key histogram TSV here")
	pkgTSV := fs.String("per-package-tsv", "", "also write the per-package TSV here")
	commit := fs.String("commit", "", "commit id to stamp (default: git rev-parse HEAD in --repo, '+dirty' if the tree is dirty)")
	if err := fs.Parse(args); err != nil {
		return err
	}
	if fs.NArg() != 1 {
		return fmt.Errorf("report needs exactly one target <dir|main.go>")
	}
	target := fs.Arg(0)
	// Host toolchain = oracle pin (the static pass reads the HOST's export
	// data for stdlib, as the frontend does; the frontend refuses on drift —
	// so does this, unless GOLEAN_ALLOW_GO_DRIFT=1 says loudly otherwise).
	pinB, err := os.ReadFile(filepath.Join(*repo, "baselines", "go-oracle-pin"))
	if err != nil {
		return fmt.Errorf("baselines/go-oracle-pin unreadable under --repo %s (%v) — refusing: the host export data cannot be certified against the pin", *repo, err)
	}
	pin := strings.TrimSpace(strings.SplitN(string(pinB), "\n", 2)[0])
	goVersion := runtime.Version()
	if goVersion != pin {
		if os.Getenv("GOLEAN_ALLOW_GO_DRIFT") != "1" {
			return fmt.Errorf("lowerdiag runs on %s but the oracle pin is %s: the stdlib view would be the host's, not the pin's — refusing (GOLEAN_ALLOW_GO_DRIFT=1 to probe loudly)", goVersion, pin)
		}
		goVersion += " (DRIFT from pin " + pin + " — GOLEAN_ALLOW_GO_DRIFT=1; not the oracle of record)"
	}
	registerPath := filepath.Join(*repo, "docs", "stdlib-admission-register.md")
	sup, err := newSupply(registerPath)
	if err != nil {
		return err
	}
	prog, err := loadProgram(target, sup)
	if err != nil {
		return err
	}
	prog.census()
	var stderrText string
	ran := false
	if *stderrFile != "" {
		b, err := os.ReadFile(*stderrFile)
		if err != nil {
			return fmt.Errorf("--frontend-stderr %s: %v", *stderrFile, err)
		}
		stderrText = string(b)
		ran = true
	}
	if *commit == "" {
		*commit = gitCommit(*repo)
	}
	rel := target
	if r, err := filepath.Rel(*repo, target); err == nil && !strings.HasPrefix(r, "..") {
		rel = r
	}
	rep := buildReport(prog, rel, *commit, goVersion, "docs/stdlib-admission-register.md", stderrText, ran)
	if *declsTSV != "" {
		if err := writeFileWith(*declsTSV, func(w *os.File) { writeDeclsTSV(w, rep) }); err != nil {
			return err
		}
	}
	if *histTSV != "" {
		if err := writeFileWith(*histTSV, func(w *os.File) { writeHistogramTSV(w, rep) }); err != nil {
			return err
		}
	}
	if *pkgTSV != "" {
		if err := writeFileWith(*pkgTSV, func(w *os.File) { writePerPackageTSV(w, rep) }); err != nil {
			return err
		}
	}
	if *asJSON {
		return writeJSON(os.Stdout, rep)
	}
	writeHuman(os.Stdout, rep)
	return nil
}

func writeFileWith(path string, f func(*os.File)) error {
	if strings.HasSuffix(path, "wire.json") || strings.HasSuffix(path, ".wire.json") {
		return fmt.Errorf("refusing to write a diagnostic under a wire file name (%s): a report must never look like a lowering", path)
	}
	w, err := os.Create(path)
	if err != nil {
		return err
	}
	f(w)
	return w.Close()
}

func gitCommit(repo string) string {
	out, err := exec.Command("git", "-C", repo, "rev-parse", "HEAD").Output()
	if err != nil {
		return "unknown"
	}
	sha := strings.TrimSpace(string(out))
	if st, err := exec.Command("git", "-C", repo, "status", "--porcelain").Output(); err == nil && strings.TrimSpace(string(st)) != "" {
		sha += "+dirty"
	}
	return sha
}

// ---- wire classification (the census's per-declaration view) ---------------

func pkgOf(name string) string {
	i := strings.Index(name, ".")
	if i < 0 {
		return "main"
	}
	head := name[:i]
	if strings.Contains(head, "/") || (head != "" && head[0] >= 'a' && head[0] <= 'z') {
		return head
	}
	return "main"
}

func classLabel(c *cause) string {
	if c == nil {
		return "UNCLASSIFIED"
	}
	return c.FR + "/" + c.ID
}

func wire(path string) error {
	b, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	var prog map[string]any
	if err := json.Unmarshal(b, &prog); err != nil {
		return err
	}
	fmt.Println("pkg\tkind\tname\tstatus\tcause\tclass\tkey")
	row := func(kind, name string, unsupported any) {
		status, causeTxt, class, key := "lowered", "-", "-", "-"
		if s, ok := unsupported.(string); ok {
			status, causeTxt = "quarantined", strings.ReplaceAll(s, "\t", " ")
			c, k := classifyText(s)
			class, key = classLabel(c), k
		}
		fmt.Printf("%s\t%s\t%s\t%s\t%s\t%s\t%s\n", pkgOf(name), kind, name, status, causeTxt, class, key)
	}
	for _, f := range asList(prog["funcs"]) {
		row("func", str(f["name"]), f["unsupported"])
	}
	for _, m := range asList(prog["methods"]) {
		if w, _ := m["wrapper"].(bool); w {
			continue // synthesized promotion wrappers are not source declarations
		}
		if _, isIface := m["interface"]; isIface {
			continue // interface method anchors
		}
		row("method", str(m["recvType"])+"."+str(m["name"]), m["unsupported"])
	}
	for _, t := range asList(prog["types"]) {
		def, _ := t["def"].(map[string]any)
		var u any
		if def != nil && str(def["kind"]) == "unsupported" {
			u = str(def["feature"])
		}
		row("type", str(t["name"]), u)
	}
	return nil
}

func classifyStdin() error {
	sc := bufio.NewScanner(os.Stdin)
	sc.Buffer(make([]byte, 1<<20), 1<<20)
	for sc.Scan() {
		c, k := classifyText(sc.Text())
		fmt.Printf("%s\t%s\n", classLabel(c), k)
	}
	return sc.Err()
}

func asList(v any) []map[string]any {
	xs, _ := v.([]any)
	out := make([]map[string]any, 0, len(xs))
	for _, x := range xs {
		if m, ok := x.(map[string]any); ok {
			out = append(out, m)
		}
	}
	return out
}

func str(v any) string {
	s, _ := v.(string)
	return s
}
