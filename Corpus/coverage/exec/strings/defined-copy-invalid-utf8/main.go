package main

// `copy` from a DEFINED string type into a DEFINED byte-slice type
// (copy's special string form, through defined types on both sides)
// preserves the raw bytes — including invalid UTF-8 and NUL — with no
// normalization or replacement-rune rewriting. Complements
// strings/defined-slice-string-conversion (CONVERSION, valid UTF-8)
// and strings/string-byte-conversion. Green cell from the external
// Codex review 2026-08-08
// (docs/2026-08-08_semantic-divergence-review.md §2).

type copySrcString string
type copyDstBytes []byte

func definedCopyInvalidUTF8() int {
	var s copySrcString = "\xff\x00A\xfe"
	b := make(copyDstBytes, 3) // short dst: copies min(len) = 3
	n := copy(b, s)
	return n*1000000 + int(b[0])*10000 + int(b[1])*100 + int(b[2]) // 3255065... compute: 3*1e6 + 255*1e4 + 0 + 65
}

func main() {
	definedCopyInvalidUTF8()
}
