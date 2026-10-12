package main

import (
	"encoding/json"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"testing"
)

// The oracle generator must not change the program (release-trust review
// 2026-10-12 F2, relayed by the [USER]). Removing the original `main` left
// `audit/side` unreferenced; the old rule DELETED the import, and Go then
// never initialized the package, so `side`'s `init` — which sets the state
// the subject reads — never ran: the original program printed 7, GoLean
// returned 7, the generated oracle observed 0. The rule now keeps such an
// import as a blank import, so the dependency and its initialization
// survive (spec «Program initialization»: every imported package is
// initialized, referenced or not).
//
// This test runs the witness both ways on the pinned Go: the ORIGINAL
// program under Go's own GOPATH resolution of its two local packages, and
// the GENERATED oracle as the runner runs it (GOPATH=<out>/gopath), and
// requires the oracle's observation to be the value the original printed.
// It also pins the structural fact (the unreferenced import is kept blank,
// the referenced one is untouched). Like the inertness test it execs `go
// run`, so the ci runs this package with -count=1 (no cached verdict for a
// result that depends on the toolchain); a missing `go` is a failure.

const importInitMain = `package main

import (
	"audit/side"
	"audit/state"
)

func Subject() int { return state.N }

func main() { _ = side.Token; println(Subject()) }
`

const importInitSide = `package side

import "audit/state"

var Token int

func init() { state.N = 7 }
`

const importInitState = `package state

var N int
`

// writeImportInitPackages lays the two local packages out under root as
// <root>/audit/side/side.go and <root>/audit/state/state.go: the case
// layout the harness copies from, and (under <gopath>/src) the layout Go
// resolves them from.
func writeImportInitPackages(t *testing.T, root string) {
	t.Helper()
	for _, f := range []struct{ rel, src string }{
		{filepath.Join("audit", "side", "side.go"), importInitSide},
		{filepath.Join("audit", "state", "state.go"), importInitState},
	} {
		path := filepath.Join(root, f.rel)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(f.src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
}

func TestBlankedImportKeepsInitialization(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Fatalf("go not on PATH: %v", err)
	}
	root := t.TempDir()
	input := filepath.Join(root, "input")
	if err := os.Mkdir(input, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(input, "main.go"), []byte(importInitMain), 0o644); err != nil {
		t.Fatal(err)
	}
	writeImportInitPackages(t, input)

	// The original program: `println` writes to stderr.
	origGopath := filepath.Join(root, "orig-gopath")
	writeImportInitPackages(t, filepath.Join(origGopath, "src"))
	stdout, stderr, exit := goRunDir(t, input, "GOPATH="+origGopath)
	if exit != 0 || len(stdout) != 0 || string(stderr) != "7\n" {
		t.Fatalf("original program: exit %d, stdout %q, stderr %q; want exit 0 and stderr \"7\\n\"", exit, stdout, stderr)
	}

	// The generated oracle for Subject.
	oracle := filepath.Join(root, "oracle")
	if err := run(config{input: filepath.Join(input, "main.go"), out: oracle, subject: "Subject", args: "-", status: "ok"}); err != nil {
		t.Fatalf("harness generation: %v", err)
	}
	// The oracle's observation is the value the original program printed.
	r := goRunOracle(t, oracle, "GOPATH="+filepath.Join(oracle, "gopath"))
	if r.exit != 0 || len(r.stderr) != 0 {
		t.Fatalf("generated oracle: exit %d, stderr %q; want a clean exit 0", r.exit, r.stderr)
	}
	if string(r.ack) != crashAckText {
		t.Fatalf("generated oracle did not register the crash channel: %q", r.ack)
	}
	var obs struct {
		Schema string `json:"schema"`
		Status string `json:"status"`
		Values []struct {
			Tag   string `json:"tag"`
			Kind  string `json:"kind"`
			Value int64  `json:"value"`
		} `json:"values"`
	}
	if err := json.Unmarshal(r.stdout, &obs); err != nil {
		t.Fatalf("generated oracle stdout is not an observation: %v: %q", err, r.stdout)
	}
	if obs.Schema != "golean-observation-v1" || obs.Status != "ok" || len(obs.Values) != 1 ||
		obs.Values[0].Tag != "int" || obs.Values[0].Kind != "int" || obs.Values[0].Value != 7 {
		t.Fatalf("generated oracle observed %s; want ok int 7, the value audit/side's init set (0 means the import, and with it the package's initialization, was dropped)", r.stdout)
	}
	// The structure behind that value: the import the surviving code no
	// longer refers to is kept as a blank import, the one it uses is
	// untouched, and both local packages are in the oracle's GOPATH.
	fset := token.NewFileSet()
	generated, err := parser.ParseFile(fset, filepath.Join(oracle, "main.go"), nil, parser.ImportsOnly)
	if err != nil {
		t.Fatal(err)
	}
	names := map[string]string{}
	for _, spec := range generated.Imports {
		path, err := strconv.Unquote(spec.Path.Value)
		if err != nil {
			t.Fatal(err)
		}
		name := ""
		if spec.Name != nil {
			name = spec.Name.Name
		}
		names[path] = name
	}
	if len(names) != 2 || names["audit/side"] != "_" || names["audit/state"] != "" {
		t.Fatalf("generated main.go imports %v; want audit/side kept as a blank import and audit/state unaliased", names)
	}
	for _, rel := range []string{filepath.Join("audit", "side", "side.go"), filepath.Join("audit", "state", "state.go")} {
		if _, err := os.Stat(filepath.Join(oracle, "gopath", "src", rel)); err != nil {
			t.Fatalf("local package not copied into the oracle's GOPATH: %v", err)
		}
	}
}
