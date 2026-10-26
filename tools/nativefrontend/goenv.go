package main

// goenv.go — the go command's CONFIGURATION channels (train-20 pre-merge
// audit F1/F2, 2026-10-26; [USER] ruling of 2026-10-26, relayed by the
// [AGENT] coordinator: read what gc reads with gc's precedence and refuse by
// name in the fail-closed direction — the BUG-135 class, a gc input the
// frontend never read moving gc's answer under a clean export).
//
// PRECEDENCE, as cfg.Getenv resolves a key (cmd/go/internal/cfg/cfg.go): the
// process environment when NON-EMPTY; else the user env file — $GOENV when
// set (`off`: no file; a path is taken as written), else
// os.UserConfigDir()/go/env — whose `KEY=value` lines (first byte A–Z) are
// what `go env -w` wrote; else $GOROOT/go.env, the toolchain's own defaults
// (GOPROXY, GOSUMDB, GOTOOLCHAIN=auto at the pin), for the keys the user
// file does not set — the GOROOT being the user file's GOROOT, else $GOROOT,
// else the go executable's install root (cfg.findGOROOT: the directory two
// or three levels above the executable that has pkg/tool; here the `go` on
// PATH, which IS the executable a consumer's `go run` would be). An
// unreadable env file is absent for gc (readEnvFile returns on any read
// error) and so here; an EMPTY process value does not shadow the file
// (measured: `GOWORK= GOFLAGS= GOENV=<file>` answers the file's values), and
// a user-file key set to the empty string does shadow GOROOT/go.env. GODEBUG
// is not a configuration key — `go env -w` refuses it and a file line never
// reaches the program (measured: BUG-135's probe stays `false`) — so it is
// read from the process environment only, and BEFORE this frontend appends
// gotypesalias=1 for its own go/types (main.go enableMaterializedAliases).
//
// THE CHANNELS, each measured on gc go1.26.5 (module mode, GOTOOLCHAIN=local,
// GOPROXY=off) with BUG-135's probe — a `go 1.26` module whose program
// reports recover()==nil after panic(nil), GOOS, GOARCH, the int width and
// x*y+z over run-time operands — and the rule each gets:
//
//	GOFLAGS      -modfile=alt.mod (process or file) makes gc read alt.mod's
//	             godebug line: `true` under a clean go.mod (audit w27/w28);
//	             a file -tags reaches the build (seen in `go build -x`). ANY
//	             non-empty value — any field after gc's own splitting
//	             (base.InitGOFLAGS: quoted.Split; whitespace alone is
//	             nothing) — is REFUSED by name: a flag changes what gc builds
//	             (-modfile, -mod, -tags, -overlay, -toolexec) or the program's
//	             meaning (-race, -gcflags); the apparatus scrubs it on every
//	             leg (scripts/go-env-pins.sh).
//	GOWORK       `off` → no workspace; empty or `auto` → the walk
//	             (modload.FindGoWork; audit F2 — `auto` was refused before);
//	             anything else names the workspace file and is refused by
//	             name without reading it — from either source: the file's
//	             GOWORK=off disables a go.work beside the module, its
//	             GOWORK=<path> selects one with no go.work in the walk
//	             (audit w12/w13, measured). modfile.go refuseWorkspace.
//	GOTOOLCHAIN  empty, local, auto, path, local+auto, local+path, and the
//	             pinned name with or without +auto/+path: gc runs the local
//	             toolchain or at most switches up to the pin (this frontend
//	             bounds the go line at the pin and refuses go.work, so `auto`
//	             has nothing newer to reach). Any other value selects or may
//	             select another toolchain — go1.24.9: a switch (stopped here
//	             by GOSUMDB=off, with network a different oracle); go1.26.4:
//	             a download attempt; bogus: «invalid GOTOOLCHAIN» — REFUSED.
//	GOOS/GOARCH  the target. The semantics is modeled and validated for
//	             linux/amd64 (the Platform instance; fileselect.go selects
//	             files for that target): GOARCH=386 changes int's width (and
//	             killed the probe with SIGTRAP), GOOS=windows builds a binary
//	             the oracle cannot run. The EFFECTIVE value — the process,
//	             the file, else gc's default, which is the host
//	             (build.Default = runtime.GOOS/GOARCH of the go binary, i.e.
//	             this process's host) — must be linux/amd64; else REFUSED.
//	GOAMD64      the codegen level: from v3 the compiler fuses x*y+z (spec:
//	             an implementation may fuse floating-point operations;
//	             measured with (1+2^-27)(1-2^-27)-1 over run-time operands:
//	             v1 and v2 print 0, v3 and v4 print -5.551115123125783e-17).
//	             Other than empty or v1: REFUSED (the oracle is pinned at v1,
//	             the toolchain's default).
//	GOEXPERIMENT a different toolchain (runtime.Version() reports
//	             go1.26.5-X:nogreenteagc; an unknown one is gc's own error,
//	             from the file too). Non-empty: REFUSED.
//	GODEBUG      panicnil=1 in the process environment flips the module-mode
//	             answer to `true` (measured). Any setting other than
//	             panicnil=0 (the apparatus's pin, docs/cli.md §1): REFUSED.
//	CGO_ENABLED  no effect on an admitted program: `import "C"` refuses at
//	             file selection and the cgo build tag is reserved (measured:
//	             CGO_ENABLED=0 prints the same). Not read.
//	GO111MODULE  `off` is GOPATH mode, where gc applies the go 1.16-era
//	             GODEBUG defaults (panicnil=1 — measured `true`, `false`
//	             with GODEBUG=panicnil=0) — the stated contract of
//	             docs/cli.md §1: the oracle runs with GODEBUG=panicnil=0 or
//	             inside a go 1.21+ module. Not refused here, since every
//	             module-less export (which gc can only build in GOPATH mode)
//	             would then need the pin in the frontend's environment too;
//	             recorded for the owner's word.
//	GOPATH       GOPATH-mode import resolution ($GOPATH/src and vendor/
//	             under it; measured: gc prints 7 for an import resolved
//	             through vendor/): an import that resolves only there
//	             refuses at type-check («could not import») — an
//	             over-refusal. Not read.
//	GOROOT       which toolchain gc runs: the apparatus checks the pin (`go
//	             version`); this frontend does not exec go and cannot see
//	             the consumer's toolchain — the standing limit, stated. Read
//	             here only to find go.env.
//	GOPROXY, GOSUMDB, GONOSUMDB, GOPRIVATE, GOINSECURE, GOCACHE, GOMODCACHE,
//	GOTMPDIR     fetching and caching: no path to the program's meaning (its
//	             imports are the pinned stdlib and case-local directories; a
//	             require that needs a lookup fails loudly under GOPROXY=off).
//	GOGC, GOMAXPROCS, GOMEMLIMIT, GOTRACEBACK   the oracle program's runtime
//	             knobs: scheduling is the membership lane's domain, crash
//	             text is pinned by the runner's GOTRACEBACK=system. Not read.
//
// Every refusal here begins `go environment: `. None is reachable from the
// apparatus, whose every `go` and frontend run pins the channels above
// (scripts/go-env-pins.sh); a consumer running the frontend in their own
// environment sees the refusal naming the channel and its source.

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
)

// The modeled target (the Platform instance: gc, linux/amd64).
const modeledGOOS, modeledGOARCH = "linux", "amd64"

func envRefuse(format string, args ...any) error {
	return unsup("go environment: "+format, args...)
}

// goEnvFilePath is the user env file as cfg.EnvFile finds it ("" = none).
func goEnvFilePath() string {
	if f := os.Getenv("GOENV"); f != "" {
		if f == "off" {
			return ""
		}
		return f
	}
	dir, err := os.UserConfigDir()
	if err != nil || dir == "" {
		return ""
	}
	return filepath.Join(dir, "go", "env")
}

// readGoEnvFile mirrors cfg.readEnvFile: `KEY=value` lines whose first byte
// is A–Z; every other line is ignored; an unreadable file is absent.
func readGoEnvFile(path string) map[string]string {
	m := map[string]string{}
	if path == "" {
		return m
	}
	data, err := os.ReadFile(path)
	if err != nil {
		return m
	}
	for len(data) > 0 {
		line := data
		if i := bytes.IndexByte(data, '\n'); i >= 0 {
			line, data = line[:i], data[i+1:]
		} else {
			data = nil
		}
		i := bytes.IndexByte(line, '=')
		if i < 0 || line[0] < 'A' || 'Z' < line[0] {
			continue
		}
		m[string(line[:i])] = string(line[i+1:])
	}
	return m
}

// goRootForEnv mirrors cfg.findGOROOT for the GOROOT whose go.env the go
// command reads: the user file's GOROOT, else $GOROOT, else the `go` on PATH
// resolved to its install root. "" when there is no go on PATH: no go command
// runs here, and there is nothing it would read.
func goRootForEnv(user map[string]string) string {
	if r := user["GOROOT"]; r != "" {
		return filepath.Clean(r)
	}
	if r := os.Getenv("GOROOT"); r != "" {
		return filepath.Clean(r)
	}
	exe, err := exec.LookPath("go")
	if err != nil {
		return ""
	}
	if exe, err = filepath.Abs(exe); err != nil {
		return ""
	}
	if resolved, err := filepath.EvalSymlinks(exe); err == nil {
		exe = resolved
	}
	for _, up := range []string{"../..", "../../.."} {
		dir := filepath.Join(exe, up)
		if fi, err := os.Stat(filepath.Join(dir, "pkg", "tool")); err == nil && fi.IsDir() {
			return dir
		}
	}
	return ""
}

// goEnv is the go command's configuration as this frontend sees it: the two
// files, loaded per call (cheap; the tests change the environment per case).
type goEnv struct {
	userPath     string
	user, goroot map[string]string
}

func loadGoEnv() goEnv {
	p := goEnvFilePath()
	user := readGoEnvFile(p)
	goroot := map[string]string{}
	if root := goRootForEnv(user); root != "" {
		goroot = readGoEnvFile(filepath.Join(root, "go.env"))
	}
	return goEnv{userPath: p, user: user, goroot: goroot}
}

// get mirrors cfg.Getenv; source says where the value came from.
func (g goEnv) get(key string) (value, source string) {
	if v := os.Getenv(key); v != "" {
		return v, "the environment"
	}
	if v, ok := g.user[key]; ok {
		return v, "the go env file " + g.userPath
	}
	if v, ok := g.goroot[key]; ok {
		return v, "the toolchain's go.env"
	}
	return "", ""
}

// goflagsSet: gc's base.InitGOFLAGS splits GOFLAGS into fields; whitespace
// alone is no flag at all.
func goflagsSet(v string) bool { return strings.TrimSpace(v) != "" }

// gotoolchainAdmitted: the values under which gc runs the local toolchain or
// at most switches to the pin (toolchain.Select: `local`, `auto`, `path`, or
// `<min>[+auto|+path]` with min `local` or a toolchain name).
func gotoolchainAdmitted(v, pin string) bool {
	switch v {
	case "", "local", "auto", "path":
		return true
	}
	min, suffix, plus := strings.Cut(v, "+")
	if plus && suffix != "auto" && suffix != "path" {
		return false
	}
	return min == "local" || min == pin
}

// godebugAdmitted: empty, or nothing but the apparatus's own pin panicnil=0.
func godebugAdmitted(v string) bool {
	for _, s := range strings.Split(v, ",") {
		if s == "" || s == "panicnil=0" {
			continue
		}
		return false
	}
	return true
}

// refuseGoEnvironment judges the channels above before a directory is
// lowered. rawGODEBUG is the process GODEBUG as the frontend was started
// (before enableMaterializedAliases appended its own setting).
func refuseGoEnvironment(rawGODEBUG string) error {
	pin, err := pinnedToolchainName()
	if err != nil {
		return err
	}
	env := loadGoEnv()
	if v, src := env.get("GOFLAGS"); goflagsSet(v) {
		return envRefuse("GOFLAGS=%q is set in %s — a flag changes what gc builds (-modfile, -mod, -tags, -overlay, -toolexec) or the program's meaning (-race, -gcflags), and none is modeled; the apparatus scrubs GOFLAGS on every leg: run gc and the frontend with it empty; refuse by name (fail closed)", v, src)
	}
	if v, src := env.get("GOTOOLCHAIN"); !gotoolchainAdmitted(v, pin) {
		return envRefuse("GOTOOLCHAIN=%q is set in %s — gc would run, or switch to, a toolchain other than the pinned %s (the admitted values: local, auto, path, local+auto, local+path, %s, %s+auto, %s+path); refuse by name (fail closed)", v, src, pin, pin, pin, pin)
	}
	goos, srcOS := env.get("GOOS")
	if goos == "" {
		goos, srcOS = runtime.GOOS, "the host default"
	}
	goarch, srcArch := env.get("GOARCH")
	if goarch == "" {
		goarch, srcArch = runtime.GOARCH, "the host default"
	}
	if goos != modeledGOOS || goarch != modeledGOARCH {
		return envRefuse("the target is %s/%s (GOOS from %s, GOARCH from %s) — the semantics is modeled and validated for %s/%s only (GOARCH=386 changes int's width, another GOOS another file set and runtime): set GOOS=%s GOARCH=%s for gc and the frontend; refuse by name (fail closed)", goos, goarch, srcOS, srcArch, modeledGOOS, modeledGOARCH, modeledGOOS, modeledGOARCH)
	}
	if v, src := env.get("GOAMD64"); v != "" && v != "v1" {
		return envRefuse("GOAMD64=%q is set in %s — from v3 the compiler fuses x*y+z (measured: a different float64 answer than v1); the oracle is pinned at the default v1; refuse by name (fail closed)", v, src)
	}
	if v, src := env.get("GOEXPERIMENT"); v != "" {
		return envRefuse("GOEXPERIMENT=%q is set in %s — a toolchain configuration the semantics is not measured against (runtime.Version() reports it as a different toolchain); refuse by name (fail closed)", v, src)
	}
	if !godebugAdmitted(rawGODEBUG) {
		return envRefuse("GODEBUG=%q is set in the environment — GODEBUG settings are not modeled: the semantics is the Go 1.26 module defaults (panic(nil) raises *runtime.PanicNilError) and the oracle is pinned with GODEBUG=panicnil=0, the one admitted setting (measured: panicnil=1 flips the answer); refuse by name (fail closed)", rawGODEBUG)
	}
	return nil
}
