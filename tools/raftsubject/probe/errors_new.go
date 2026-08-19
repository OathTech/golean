// PROBE ARTEFACT — not part of the subject tree, never derived into it.
//
// The frontier walk injects this file to stand in for `errors.New` at the
// NINE package-level `var Err… = errors.New(…)` initializers of the vendored
// raft root package.  Those nine are export-BLOCKING rather than quarantined:
// a package-level variable has no body to replace with a refusing stub, so
// one unlowerable initializer refuses the whole export (docs/raft-w3-log.md,
// gap G-2/G-3).  The walk rewrites exactly those nine call sites to this
// constructor and leaves every errors.New inside a function body alone, so
// the census still reports which declarations `errors.New` quarantines.
//
// The body is Go's own: `errors.New` returns a pointer to a struct holding
// the string (deps/go/src/errors/errors.go), so pointer identity distinguishes
// two errors with equal text — which is what raft's `err == ErrCompacted`
// comparisons rely on.  That makes this a faithful stand-in AND the shape the
// E5 stdlib shim would take if `errors.New` is admitted to the allowlist.
package raft

type goleanProbeErrorString struct{ s string }

func (e *goleanProbeErrorString) Error() string { return e.s }

func goleanProbeErrorsNew(text string) error { return &goleanProbeErrorString{s: text} }
