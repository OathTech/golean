#!/usr/bin/env bash
# go build's report of a child killed by a signal, in module and GOPATH mode, through a -toolexec
# wrapper that kills itself; `go run` of a program that SIGKILLs itself; and the negative runner's
# regex (scripts/coverage-negative, the go-crash stage) against each output.
set -u
HERE="$(cd "$(dirname "$0")" && pwd -P)"; T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT
mkdir -p "$T/mod" "$T/gopath" "$T/self"
printf 'package main\n\nfunc main() { println(1) }\n' > "$T/mod/main.go"; printf 'module test\ngo 1.26\n' > "$T/mod/go.mod"; cp "$T/mod/main.go" "$T/gopath/"
printf 'package main\n\nimport (\n\t"os"\n\t"syscall"\n)\n\nfunc main() { println("before"); syscall.Kill(os.Getpid(), syscall.SIGKILL) }\n' > "$T/self/main.go"
RE='(^|: )signal: [a-z][a-z0-9/ ]*( \(core dumped\))?$'
judge() { printf '%s\n' "$1" | grep -aEm1 "$RE" >/dev/null && echo "  regex: MATCH" || echo "  regex: no match"; }
for w in killme termme segvme; do echo "## module mode, go build -toolexec=$w.sh"; out=$(cd "$T/mod" && env GO111MODULE=on GOFLAGS= GOWORK=off GOPROXY=off GOTOOLCHAIN=local GOCACHE="$T/cache" go build -toolexec="$HERE/$w.sh" -o "$T/bin" . 2>&1); echo "rc=$?"; printf '%s\n' "$out" | sed 's/^/  |/'; judge "$out"; done
echo "## GOPATH mode, go build -toolexec=killme.sh"; out=$(cd "$T" && env GO111MODULE=off GOFLAGS= GOWORK=off GOCACHE="$T/cache" go build -toolexec="$HERE/killme.sh" -o "$T/bin" ./gopath 2>&1); echo "rc=$?"; printf '%s\n' "$out" | sed 's/^/  |/'; judge "$out"
echo "## go run of a program that SIGKILLs itself (the positive runner's shape: no 'exit status N' trailer)"; out=$(cd "$T/self" && env GO111MODULE=off GOFLAGS= GOWORK=off GOCACHE="$T/cache" go run . 2>&1); echo "rc=$?"; printf '%s\n' "$out" | sed 's/^/  |/'
