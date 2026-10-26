package main

// Unit tests for the go command's configuration channels (goenv.go; train-20
// pre-merge audit F1/F2, BUG-135). Each case pins the whole environment it
// depends on with t.Setenv (TestMain pins GOENV=off, GOFLAGS and GOWORK for
// every other test), so a box's `go env -w` settings and an ambient
// GOFLAGS/GOWORK/GOOS reach no case.

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// cleanGoEnv pins every channel refuseGoEnvironment reads to an admitted
// value; a case then moves one of them.
func cleanGoEnv(t *testing.T) {
	t.Helper()
	for k, v := range map[string]string{
		"GOENV": "off", "GOFLAGS": "", "GOWORK": "", "GOTOOLCHAIN": "local",
		"GOOS": "linux", "GOARCH": "amd64", "GOAMD64": "", "GOEXPERIMENT": "", "GOROOT": "",
	} {
		t.Setenv(k, v)
	}
}

func wantEnvRefusal(t *testing.T, err error, names ...string) {
	t.Helper()
	if err == nil {
		t.Fatalf("expected a refusal naming %q", names)
	}
	if !strings.HasPrefix(err.Error(), "native frontend unsupported: go environment: ") {
		t.Fatalf("refusal %q lacks the `go environment: ` prefix", err.Error())
	}
	for _, n := range names {
		if !strings.Contains(err.Error(), n) {
			t.Fatalf("refusal %q does not name %q", err.Error(), n)
		}
	}
}

// envFileFixture writes a go env file (the `go env -w` format: KEY=value
// lines) and points GOENV at it.
func envFileFixture(t *testing.T, lines ...string) string {
	t.Helper()
	p := filepath.Join(t.TempDir(), "env")
	if err := os.WriteFile(p, []byte(strings.Join(lines, "\n")+"\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	t.Setenv("GOENV", p)
	return p
}

func TestGoEnvironmentRefusal(t *testing.T) {
	cases := []struct {
		label string
		set   func(t *testing.T) // on top of cleanGoEnv
		debug string             // the raw process GODEBUG
		want  []string           // "" = accepted
	}{
		{"clean: accepted", func(*testing.T) {}, "", nil},
		{"GODEBUG=panicnil=0, the apparatus's pin: accepted", func(*testing.T) {}, "panicnil=0", nil},
		{"GODEBUG=panicnil=1 (measured: flips the module-mode answer)", func(*testing.T) {}, "panicnil=1", []string{"GODEBUG=\"panicnil=1\""}},
		{"GODEBUG with another setting", func(*testing.T) {}, "panicnil=0,http2debug=1", []string{"GODEBUG="}},
		// GOFLAGS: the audit's w27 (process) and w28 (the file); whitespace is nothing.
		{"process GOFLAGS=-modfile=alt.mod (audit w27)", func(t *testing.T) { t.Setenv("GOFLAGS", "-modfile=alt.mod") }, "", []string{"GOFLAGS=\"-modfile=alt.mod\"", "the environment"}},
		{"process GOFLAGS of whitespace only: no flag (gc's quoted.Split)", func(t *testing.T) { t.Setenv("GOFLAGS", "  ") }, "", nil},
		{"the env file's GOFLAGS=-modfile=alt.mod (audit w28)", func(t *testing.T) { envFileFixture(t, "GOFLAGS=-modfile=alt.mod") }, "", []string{"GOFLAGS=\"-modfile=alt.mod\"", "the go env file "}},
		{"an empty process GOFLAGS does not shadow the file (cfg.Getenv)", func(t *testing.T) { t.Setenv("GOFLAGS", ""); envFileFixture(t, "GOFLAGS=-tags=x") }, "", []string{"GOFLAGS=\"-tags=x\"", "the go env file "}},
		{"a whitespace process GOFLAGS does shadow the file", func(t *testing.T) { t.Setenv("GOFLAGS", " "); envFileFixture(t, "GOFLAGS=-tags=x") }, "", nil},
		{"the file: comments and lowercase lines are ignored, as gc ignores them", func(t *testing.T) { envFileFixture(t, "# a comment", "goflags=-tags=x", "GOFLAGS") }, "", nil},
		{"GOENV naming a missing file: absent for gc, absent here", func(t *testing.T) { t.Setenv("GOENV", filepath.Join(t.TempDir(), "absent")) }, "", nil},
		{"GOENV naming a directory: absent for gc, absent here", func(t *testing.T) { t.Setenv("GOENV", t.TempDir()) }, "", nil},
		// GOTOOLCHAIN.
		{"GOTOOLCHAIN=auto", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "auto") }, "", nil},
		{"GOTOOLCHAIN=path", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "path") }, "", nil},
		{"GOTOOLCHAIN=local+auto", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "local+auto") }, "", nil},
		{"GOTOOLCHAIN=<the pin>", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "go1.26.5") }, "", nil},
		{"GOTOOLCHAIN=<the pin>+auto", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "go1.26.5+auto") }, "", nil},
		{"GOTOOLCHAIN unset everywhere (gc: no switching)", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "") }, "", nil},
		{"GOTOOLCHAIN=go1.24.9 (measured: a switch attempt)", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "go1.24.9") }, "", []string{"GOTOOLCHAIN=\"go1.24.9\""}},
		{"GOTOOLCHAIN=go1.26.4 (a download attempt)", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "go1.26.4") }, "", []string{"GOTOOLCHAIN=\"go1.26.4\""}},
		{"GOTOOLCHAIN=bogus (gc: «invalid GOTOOLCHAIN»)", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "bogus") }, "", []string{"GOTOOLCHAIN=\"bogus\""}},
		{"GOTOOLCHAIN=go1.26.5+foo (gc: only +auto and +path)", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", "go1.26.5+foo") }, "", []string{"GOTOOLCHAIN=\"go1.26.5+foo\""}},
		{"the file's GOTOOLCHAIN=go1.99.0", func(t *testing.T) { t.Setenv("GOTOOLCHAIN", ""); envFileFixture(t, "GOTOOLCHAIN=go1.99.0") }, "", []string{"GOTOOLCHAIN=\"go1.99.0\"", "the go env file "}},
		// GOOS / GOARCH / GOAMD64 / GOEXPERIMENT.
		{"GOOS=windows (measured: an unrunnable binary)", func(t *testing.T) { t.Setenv("GOOS", "windows") }, "", []string{"the target is windows/amd64", "GOOS from the environment"}},
		{"the file's GOARCH=386 (measured: int's width)", func(t *testing.T) { t.Setenv("GOARCH", ""); envFileFixture(t, "GOARCH=386") }, "", []string{"the target is linux/386", "GOARCH from the go env file"}},
		{"GOAMD64=v1", func(t *testing.T) { t.Setenv("GOAMD64", "v1") }, "", nil},
		{"GOAMD64=v3 (measured: fused multiply-add)", func(t *testing.T) { t.Setenv("GOAMD64", "v3") }, "", []string{"GOAMD64=\"v3\""}},
		{"the file's GOAMD64=v4", func(t *testing.T) { envFileFixture(t, "GOAMD64=v4") }, "", []string{"GOAMD64=\"v4\"", "the go env file "}},
		{"GOEXPERIMENT=nogreenteagc (a different toolchain)", func(t *testing.T) { t.Setenv("GOEXPERIMENT", "nogreenteagc") }, "", []string{"GOEXPERIMENT=\"nogreenteagc\""}},
		{"the file's GOEXPERIMENT=foo", func(t *testing.T) { envFileFixture(t, "GOEXPERIMENT=foo") }, "", []string{"GOEXPERIMENT=\"foo\"", "the go env file "}},
	}
	for _, c := range cases {
		t.Run(c.label, func(t *testing.T) {
			cleanGoEnv(t)
			c.set(t)
			err := refuseGoEnvironment(c.debug)
			if c.want == nil {
				if err != nil {
					t.Fatalf("expected acceptance, got %v", err)
				}
				return
			}
			wantEnvRefusal(t, err, c.want...)
		})
	}
}

// The toolchain's own go.env (GOROOT/go.env) is the third source, for keys
// the user file does not set — and a user-file key set to the EMPTY string
// shadows it (measured: `GOTOOLCHAIN=` in the user file answers empty where
// go.env says auto).
func TestGoEnvironmentGorootGoEnv(t *testing.T) {
	cleanGoEnv(t)
	root := t.TempDir()
	if err := os.MkdirAll(filepath.Join(root, "pkg", "tool"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(root, "go.env"), []byte("# the toolchain's defaults\nGOFLAGS=-tags=x\nGOTOOLCHAIN=auto\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	t.Setenv("GOROOT", root)
	wantEnvRefusal(t, refuseGoEnvironment(""), "GOFLAGS=\"-tags=x\"", "the toolchain's go.env")
	// The user file's empty GOFLAGS= shadows GOROOT/go.env.
	envFileFixture(t, "GOFLAGS=")
	if err := refuseGoEnvironment(""); err != nil {
		t.Fatalf("the user file's empty value should shadow go.env: %v", err)
	}
	// The user file's GOROOT names the toolchain whose go.env is read.
	t.Setenv("GOROOT", "")
	envFileFixture(t, "GOROOT="+root)
	wantEnvRefusal(t, refuseGoEnvironment(""), "GOFLAGS=\"-tags=x\"", "the toolchain's go.env")
}

// GOWORK through the same precedence (audit F1 w12/w13, F2): the file's
// GOWORK=off disables a workspace beside the module, its GOWORK=<path>
// selects one with no go.work in the walk, and `auto` is the walk.
func TestWorkspaceThroughGoEnv(t *testing.T) {
	const goMod = "module test\ngo 1.26\n"
	const src = "package main\n\nfunc main() { println(1) }\n"
	t.Run("the file's GOWORK=off disables a go.work beside the module (audit w12)", func(t *testing.T) {
		cleanGoEnv(t)
		dir := writeDir(t, map[string]string{"main.go": src, "go.mod": goMod, "go.work": "go 1.26\nuse .\ngodebug panicnil=1\n"})
		envFileFixture(t, "GOWORK=off")
		if err := refuseForeignModuleVersion(dir); err != nil {
			t.Fatalf("expected acceptance under the file's GOWORK=off, got %v", err)
		}
	})
	t.Run("the file's GOWORK=<path> with no go.work in the walk (audit w13)", func(t *testing.T) {
		cleanGoEnv(t)
		dir := writeDir(t, map[string]string{"main.go": src, "go.mod": goMod})
		requireNoWorkspaceAbove(t, dir)
		elsewhere := filepath.Join(t.TempDir(), "go.work")
		if err := os.WriteFile(elsewhere, []byte("go 1.26\nuse "+dir+"\ngodebug panicnil=1\n"), 0o644); err != nil {
			t.Fatal(err)
		}
		p := envFileFixture(t, "GOWORK="+elsewhere)
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(dir), "GOWORK="+elsewhere, "from the go env file "+p)
	})
	t.Run("process GOWORK=auto is the walk: no go.work, accepted (audit w04)", func(t *testing.T) {
		cleanGoEnv(t)
		t.Setenv("GOWORK", "auto")
		dir := writeDir(t, map[string]string{"main.go": src, "go.mod": goMod})
		requireNoWorkspaceAbove(t, dir)
		if err := refuseForeignModuleVersion(dir); err != nil {
			t.Fatalf("GOWORK=auto with no go.work: expected acceptance, got %v", err)
		}
	})
	t.Run("process GOWORK=auto is the walk: go.work beside, refused (audit w05)", func(t *testing.T) {
		cleanGoEnv(t)
		t.Setenv("GOWORK", "auto")
		dir := writeDir(t, map[string]string{"main.go": src, "go.mod": goMod, "go.work": "go 1.26\nuse .\n"})
		requireNoWorkspaceAbove(t, dir)
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(dir), "is inside the workspace "+filepath.Join(dir, "go.work"))
	})
	t.Run("the file's GOWORK=auto is the walk too", func(t *testing.T) {
		cleanGoEnv(t)
		dir := writeDir(t, map[string]string{"main.go": src, "go.mod": goMod, "go.work": "go 1.26\nuse .\n"})
		requireNoWorkspaceAbove(t, dir)
		envFileFixture(t, "GOWORK=auto")
		wantWorkspaceRefusal(t, refuseForeignModuleVersion(dir), "is inside the workspace "+filepath.Join(dir, "go.work"))
	})
	t.Run("process GOWORK=off shadows the file's GOWORK=<path>", func(t *testing.T) {
		cleanGoEnv(t)
		dir := writeDir(t, map[string]string{"main.go": src, "go.mod": goMod})
		envFileFixture(t, "GOWORK=/nonexistent/go.work")
		t.Setenv("GOWORK", "off")
		if err := refuseForeignModuleVersion(dir); err != nil {
			t.Fatalf("expected acceptance, got %v", err)
		}
	})
}
