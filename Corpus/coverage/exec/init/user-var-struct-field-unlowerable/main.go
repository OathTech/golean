// FR-24's neighbour, NOT closed by FR-24 (2026-09-04, lane fr24): the
// unlowerable type sits in a FIELD of a source-declared struct type, and
// the package var is of that struct type. The var's own emitType lowers
// (a `named` reference — the struct TypeDef is emitted by the type-
// declaration pass), so the FR-24 poison never arms; the TypeDef pass
// then refuses the whole export at the field (emit.go emitGenDeclTypes:
// a struct field type that does not lower has no per-declaration
// quarantine). Rowed as its own frontier item (a TYPE-declaration kill,
// a different mechanism from FR-24's var poison). Legal Go; gc PASS.
package main

import "sync"

type holder struct {
	m sync.Map
	n int
}

var h holder

func unrelated() int { return 7 }

func main() { h.n = 1; println(unrelated(), h.n) }
