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
	// 256-base packing — injective per byte (values up to 255 never
	// alias): 3*2^24 + 255*2^16 + 0*256 + 65 = 67043393.
	return n*16777216 + int(b[0])*65536 + int(b[1])*256 + int(b[2])
}

func main() {
	definedCopyInvalidUTF8()
}
