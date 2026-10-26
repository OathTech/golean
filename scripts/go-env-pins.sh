# scripts/go-env-pins.sh — the go environment every apparatus `go` and native-frontend run is
# pinned to. SOURCED by the gate, the runners, every check script and every instrument — early,
# before any `cd`, through its own location: `. "$(dirname "${BASH_SOURCE[0]}")/go-env-pins.sh"`
# (train-19 shake review F7 and train-20 pre-merge audit F1/F3, 2026-10-26).
#
# WHY: the go command reads its configuration from the process environment, else its env file
# (`go env -w`, $GOENV), else $GOROOT/go.env, and each channel moves what gc builds or what the
# program means (tools/nativefrontend/goenv.go carries the measured table): GOFLAGS (-modfile,
# -tags, -toolexec…), GOWORK (a workspace's godebug/go/toolchain lines), GOTOOLCHAIN (a switch to
# another toolchain), GOOS/GOARCH (the target — the semantics is linux/amd64), GOAMD64 (fused
# multiply-add from v3), GOEXPERIMENT (a different toolchain), GODEBUG (panicnil). The frontend
# refuses each by name; the apparatus pins each, so no box's environment or env file moves a
# verdict and the frontend's refusals are unreachable from the gate (scripts/test-oracle-env is
# the self-test: the fast tier under a hostile environment, every verdict unchanged).
#
# HOW: `export $GO_ENV_PINS` right after sourcing pins the sourcing script's whole process tree;
# the runners and the gate also prefix their verdict-bearing commands with `env $GO_ENV_PINS …`
# (unquoted on purpose: the words are the assignments, none holds a space) so the pin is visible
# at the site. A later assignment on the same `env` line overrides a pin where a leg needs
# another value (the positive oracle's GODEBUG=panicnil=0, the oracle-toolchain switch's
# GOTOOLCHAIN=<version>). GOENV=off takes the env file out of the picture entirely, so a key it
# could set that is not listed here cannot reach a `go` either. GOOS=linux GOARCH=amd64 is the
# oracle's platform: on another host the Go steps cross-compile and cannot run — by design, the
# gate needs the pinned platform.
GO_ENV_PINS="GOFLAGS= GOWORK=off GOENV=off GOTOOLCHAIN=local GOOS=linux GOARCH=amd64 GOAMD64=v1 GOEXPERIMENT= GODEBUG="
export GO_ENV_PINS
