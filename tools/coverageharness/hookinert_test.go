package main

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

// A-R9 (landing review 2026-09-07, chunk L4 [AGENT]): the oracle program is
// rewritten before compilation — the generated wrapper's main (and, for the
// diagnostic tools' --copy-oracle, a fresh copy's own main) begins with
// _goleanSetupCrash(). TestOracleCopyPreservesSemanticSources proves the
// SOURCE side (the semantic input is untouched; the edit is exactly the
// insertion). This test proves the OBSERVATION side, on real pinned Go: the
// same subject, run with the hook's body emptied (identical source layout,
// so even the trace's line numbers agree), yields byte-identical stdout,
// exit status, go run trailer, and stderr up to the runtime's trace header —
// every byte the observer reads (program output, panic/fatal message
// region). Only the trace frames are excluded: they carry addresses that
// differ between two runs of the SAME binary, and no observation reads them.
// The test also checks the hook DID act on the instrumented side (the
// channel is registered, and non-empty on a runtime abort), so the two
// variants differ in the hook alone.
//
// It runs `go run` on the pinned toolchain; a missing `go` is a failure, not
// a skip (a gate that cannot run fails). GOCACHE follows the repo convention
// (docs/architecture-rules.md, formerly AGENTS.md): the environment's, else
// <repo>/artifacts/go-build-cache.

const inertFixture = `package main

import "sync"

func subjOk() int   { print("out\x00\x01\t\r\n"); return 7 }
func subjPanic()    { print("before\n"); panic("boom\x00\nsecond") }
func subjFatal()    { var m sync.Mutex; m.Unlock() }
func subjDeadlock() { select {} }
func subjUnwind()   { var m sync.Mutex; defer m.Unlock(); panic("during unwind") }

func main() {}
`

const inertNoopHook = "package main\n\nfunc _goleanSetupCrash() {}\n"

type oracleRun struct {
	stdout, stderr []byte
	exit           int
	crash, ack     []byte
}

func goRunOracle(t *testing.T, dir string) oracleRun {
	t.Helper()
	for _, name := range []string{"oracle.crash", "oracle.registered"} {
		if err := os.WriteFile(filepath.Join(dir, name), nil, 0o600); err != nil {
			t.Fatal(err)
		}
	}
	cache := os.Getenv("GOCACHE")
	if cache == "" {
		abs, err := filepath.Abs(filepath.Join("..", "..", "artifacts", "go-build-cache"))
		if err != nil {
			t.Fatal(err)
		}
		cache = abs
	}
	if err := os.MkdirAll(cache, 0o755); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "run", ".")
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), "GO111MODULE=off", "GOFLAGS=", "GODEBUG=panicnil=0", "GOTRACEBACK=system", "GOCACHE="+cache)
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	err := cmd.Run()
	if err != nil {
		if _, ok := err.(*exec.ExitError); !ok {
			t.Fatalf("go run could not start in %s: %v", dir, err)
		}
	}
	r := oracleRun{stdout: stdout.Bytes(), stderr: stderr.Bytes(), exit: cmd.ProcessState.ExitCode()}
	var rerr error
	if r.crash, rerr = os.ReadFile(filepath.Join(dir, "oracle.crash")); rerr != nil {
		t.Fatal(rerr)
	}
	if r.ack, rerr = os.ReadFile(filepath.Join(dir, "oracle.registered")); rerr != nil {
		t.Fatal(rerr)
	}
	return r
}

// observedBytes returns what the observer reads from stderr: the whole
// stream for a run with no runtime trace, else the bytes before the first
// trace header plus go run's trailer.
func observedBytes(t *testing.T, label string, stderr []byte, abort bool) []byte {
	t.Helper()
	m := abortTraceHeaderRe.FindIndex(stderr)
	if !abort {
		if m != nil {
			t.Fatalf("%s: unexpected runtime trace in an ok run: %q", label, stderr)
		}
		return stderr
	}
	if m == nil {
		t.Fatalf("%s: no runtime trace header in an aborting run: %q", label, stderr)
	}
	trailer := []byte("\nexit status 2\n")
	if !bytes.HasSuffix(stderr, trailer) {
		t.Fatalf("%s: aborting run without the child's exit status 2 trailer: %q", label, stderr)
	}
	return append(append([]byte{}, stderr[:m[0]]...), trailer...)
}

func requireInert(t *testing.T, label string, hooked, plain oracleRun, abort bool) {
	t.Helper()
	if hooked.exit != plain.exit {
		t.Fatalf("%s: exit status differs with the hook: %d vs %d", label, hooked.exit, plain.exit)
	}
	if !bytes.Equal(hooked.stdout, plain.stdout) {
		t.Fatalf("%s: stdout differs with the hook: %q vs %q", label, hooked.stdout, plain.stdout)
	}
	ho, po := observedBytes(t, label+"/hooked", hooked.stderr, abort), observedBytes(t, label+"/plain", plain.stderr, abort)
	if !bytes.Equal(ho, po) {
		t.Fatalf("%s: observed stderr bytes differ with the hook:\n%q\nvs\n%q", label, ho, po)
	}
	// The hook acted on the instrumented side, and only there.
	if !bytes.Equal(hooked.ack, []byte(crashAckText)) {
		t.Fatalf("%s: instrumented run did not register the crash channel: %q", label, hooked.ack)
	}
	if abort && len(hooked.crash) == 0 {
		t.Fatalf("%s: instrumented abort wrote no crash report — the hook was not live", label)
	}
	if !abort && len(hooked.crash) != 0 {
		t.Fatalf("%s: instrumented ok run wrote a crash report: %q", label, hooked.crash)
	}
	if len(plain.ack) != 0 || len(plain.crash) != 0 {
		t.Fatalf("%s: the no-op variant touched the channel files", label)
	}
}

func TestCrashHookInertOnObservation(t *testing.T) {
	if _, err := exec.LookPath("go"); err != nil {
		t.Fatalf("go not on PATH: %v", err)
	}
	root := t.TempDir()
	input := filepath.Join(root, "input")
	if err := os.Mkdir(input, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(input, "main.go"), []byte(inertFixture), 0o644); err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		subject, status string
		kind            string // checkedAbortView's verdict on the hooked run, "" = no verdict expected
	}{
		{"subjOk", "ok", ""},
		{"subjPanic", "panic", "panic"},
		{"subjFatal", "fatal", "fatal"},
		{"subjDeadlock", "deadlock", "deadlock"},
		// BUG-106's shape: the hook is live (non-empty channel) but the
		// message region precedes m.dying, so classification refuses; the
		// observation bytes are still inert.
		{"subjUnwind", "fatal", ""},
	} {
		hookedDir := filepath.Join(root, tc.subject+"-hooked")
		if err := run(config{input: filepath.Join(input, "main.go"), out: hookedDir, subject: tc.subject, args: "-", status: tc.status}); err != nil {
			t.Fatalf("%s: harness generation: %v", tc.subject, err)
		}
		plainDir := filepath.Join(root, tc.subject+"-plain")
		copyDirReplacingHook(t, hookedDir, plainDir)
		hooked, plain := goRunOracle(t, hookedDir), goRunOracle(t, plainDir)
		abort := tc.status != "ok"
		requireInert(t, tc.subject, hooked, plain, abort)
		if tc.kind != "" {
			v, err := checkedAbortView(hooked.stderr, crashEvidence{true, hooked.crash, hooked.ack})
			if err != nil || v.kind != tc.kind {
				t.Fatalf("%s: hooked run must classify as %s: %+v/%v", tc.subject, tc.kind, v, err)
			}
		}
	}
}

// The diagnostic tools' --copy-oracle splices the call into a user main.
// Compared against the PRISTINE package (no insertion at all): the
// observation bytes are identical; only the trace's line numbers move.
func TestOracleCopyInertOnObservation(t *testing.T) {
	root := t.TempDir()
	pristine := filepath.Join(root, "pristine")
	if err := os.Mkdir(pristine, 0o755); err != nil {
		t.Fatal(err)
	}
	src := "package main\n\nfunc main() {\n\tprint(\"glued\")\n\tpanic(\"actual\\x00\\nsecond\")\n}\n"
	if err := os.WriteFile(filepath.Join(pristine, "main.go"), []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	copied := filepath.Join(root, "copied")
	if err := copyOraclePackage(pristine, copied); err != nil {
		t.Fatal(err)
	}
	hooked, plain := goRunOracle(t, copied), goRunOracle(t, pristine)
	requireInert(t, "copy-oracle", hooked, plain, true)
	v, err := checkedAbortView(hooked.stderr, crashEvidence{true, hooked.crash, hooked.ack})
	if err != nil || v.kind != "panic" || string(v.output) != "glued" || string(v.message) != "actual\x00" {
		t.Fatalf("copy-oracle: hooked run must classify with the exact partition: %+v/%v", v, err)
	}
}

func copyDirReplacingHook(t *testing.T, from, to string) {
	t.Helper()
	if err := os.Mkdir(to, 0o755); err != nil {
		t.Fatal(err)
	}
	entries, err := os.ReadDir(from)
	if err != nil {
		t.Fatal(err)
	}
	for _, e := range entries {
		if e.IsDir() {
			continue
		}
		data, err := os.ReadFile(filepath.Join(from, e.Name()))
		if err != nil {
			t.Fatal(err)
		}
		if e.Name() == crashHelperName {
			data = []byte(inertNoopHook)
		}
		if err := os.WriteFile(filepath.Join(to, e.Name()), data, 0o644); err != nil {
			t.Fatal(err)
		}
	}
}
