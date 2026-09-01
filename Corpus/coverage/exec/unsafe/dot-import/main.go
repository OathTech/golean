package main

import . "unsafe"

// UNSAFE DOT-IMPORT REFUSAL PIN (audit fix round 2026-09-01; probe
// u2): `import . "unsafe"` makes Sizeof/Offsetof/Alignof BARE
// identifiers, outside the selector-based checkUnsafeLayoutOps scan
// (emit.go) — pre-fix this program EXPORTED and the folded
// implementation-specific layout constant entered the model silently,
// the exact leak BUG-070 closed for the selector form. Dot-imports of
// unsafe are now refused OUTRIGHT, before the selector walk. RED
// (frontend-export) BY DESIGN. gc @ go1.26.5 on amd64: 16.

type s struct {
	a int32
	b int64
}

func dotImportSizeof() int {
	return int(Sizeof(s{})) // gc amd64: 16
}

func main() { dotImportSizeof() }
