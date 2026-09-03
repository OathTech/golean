// FR-22 witness — a package-level var initializer calling a stdlib
// function outside H-11's pureUnmodeledCallees allowlist (time.Date) is a
// WHOLE-EXPORT refusal today: the subject below never touches the var,
// yet cannot be lowered. Shape lifted from cedar-go types/datetime.go:16
// (census 2026-09-03). Legal Go; gc PASS expected.
package main

import "time"

// A pure, deterministic constant initializer (spec#Package_initialization:
// initialized in dependency order before main; no observable effect).
var maxDatetime = time.Date(292278994, 8, 17, 7, 12, 55, 807*1e6, time.UTC)

func unrelatedToTheInitializer() int {
	return 42
}

func main() {}
