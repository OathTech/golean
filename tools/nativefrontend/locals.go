package main

// locals.go — per-function numbering of locals (B6, window row 5, 2026-09-30;
// design note docs/2026-09-30_numeric-locals-design.md).
//
// Every go/types object a function declares or uses as a LOCAL — its receiver,
// parameters, results, the capture pointers of a lifted literal, and its body's
// `:=` / var / range / select / type-switch binders — gets one DECLARATION index
// in that function's name table, allotted at first encounter. Ids are per
// OBJECT: a `:=` that reuses `err` is a go/types use, not a definition, and the
// per-iteration loop copy (emitFor's loopVar) re-declares the same object in a
// nested scope, so one id may have several declaration sites; the machine's
// scope walk (innermost binding of that id) keeps today's meaning. Two shadowing
// `x`s are two objects, two ids. Every wire node that spells a source local
// carries its index beside the spelling ("local", or "keyLocal"/"valLocal" on a
// range); `$`-temporaries carry NONE — the decoder interns them after the table.
// The decoder cross-checks each reference against its own scope-exact lexical
// environment: the innermost in-scope declaration of the same spelling must be
// this very object, or the program refuses by name (design D1, the pure-renaming
// certificate). Numeric ids stable across source edits are NOT an API promise.

import (
	"go/types"
	"path/filepath"
	"strconv"
)

// beginLocals opens a fresh name table (a function's start).
func (e *emitter) beginLocals() {
	e.localIDs = map[types.Object]int{}
	e.localTable = []any{}
}

// freshLocals saves the current table (an enclosing function's, when a lifted
// literal or a stub is emitted inside a body) and opens a fresh one; the returned
// function restores the saved table.
func (e *emitter) freshLocals() func() {
	savedIDs, savedTable := e.localIDs, e.localTable
	e.beginLocals()
	return func() { e.localIDs, e.localTable = savedIDs, savedTable }
}

// localsTable is the wire's "locals" value for the current function: the entries
// in allotment order (never nil — an empty table is `[]`).
func (e *emitter) localsTable() []any {
	if e.localTable == nil {
		return []any{}
	}
	return e.localTable
}

// localID returns obj's declaration index in the current function's table,
// allotting one on first encounter with the given kind (recv | param | result |
// capture | local) and the lowering's spelling `wire` (recorded only when it
// differs from Go's identifier — a shadow rename, a capture pointer). The entry
// keeps the SOURCE spelling (obj.Name()) and the declaring identifier's position
// as `basename.go:line:col`.
func (e *emitter) localID(obj types.Object, kind, wire string) int {
	if e.localIDs == nil {
		e.beginLocals()
	}
	if id, ok := e.localIDs[obj]; ok {
		return id
	}
	id := len(e.localTable)
	entry := map[string]any{"name": obj.Name(), "kind": kind}
	if e.fset != nil {
		if p := e.fset.Position(obj.Pos()); p.IsValid() {
			entry["pos"] = filepath.Base(p.Filename) + ":" + strconv.Itoa(p.Line) + ":" + strconv.Itoa(p.Column)
		}
	}
	if wire != "" && wire != obj.Name() {
		entry["wire"] = wire
	}
	e.localIDs[obj] = id
	e.localTable = append(e.localTable, entry)
	return id
}

// localIdent is a reference node for a resolved local object: the lowering's
// spelling plus its declaration index.
func (e *emitter) localIdent(obj types.Object, spelling string) map[string]any {
	return map[string]any{"expr": "ident", "name": spelling, "local": e.localID(obj, "local", spelling)}
}
