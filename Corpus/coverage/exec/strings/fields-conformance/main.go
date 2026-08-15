package main

import (
	"fmt"
	"strings"
)

// strings.Fields conformance pins (extension E5). The oracle runs the
// REAL strings.Fields; the machine runs the frontend's shim — so each
// row here is a direct differential test of shim fidelity against the
// stdlib's documented behavior ("splits ... around each instance of
// one or more consecutive white space characters, as defined by
// unicode.IsSpace, returning ... an empty slice if s contains only
// white space").
//
// fieldsJoin observes the SPLIT byte-exactly, not just the count: the
// fields re-joined with '|' (a byte that occurs in no input below).
func fieldsJoin(s string) (uint64, string) {
	f := strings.Fields(s)
	out := ""
	for i := 0; i < len(f); i++ {
		if i > 0 {
			out += "|"
		}
		out += f[i]
	}
	return uint64(len(f)), out
}

// The empty string: no fields.
func fcEmpty() (uint64, string) { return fieldsJoin("") }

// Only white space (every ASCII member of the class): no fields.
func fcAllSpace() (uint64, string) { return fieldsJoin(" \t\n\v\f\r ") }

// No separators at all: one field, the whole string.
func fcSingle() (uint64, string) { return fieldsJoin("abc") }

// Leading and trailing runs, consecutive interior spaces.
func fcLeadTrail() (uint64, string) { return fieldsJoin("  ab  cd  ") }

// Mixed consecutive separators: tab/space/newline/CR/VT runs.
func fcConsecMixed() (uint64, string) { return fieldsJoin("a\t\tb \n c\r\vd") }

// The NON-ASCII members of unicode.IsSpace: NBSP (U+00A0), NEL
// (U+0085), EM SPACE (U+2003, a Zs representative), IDEOGRAPHIC
// SPACE (U+3000). Real Fields splits on ALL of these; the shim must
// too.
func fcUnicodeSpace() (uint64, string) { return fieldsJoin("a\u00a0bc\u0085d\u2003d\u3000e") }

// The NEGATIVE pin: non-ASCII runes that are NOT white space — ZERO
// WIDTH SPACE (U+200B, adjacent to the Zs block but White_Space=No)
// and ÿ (U+00FF, a C2/C3-lead multi-byte rune) — must NOT split.
func fcUnicodeNonSpace() (uint64, string) { return fieldsJoin("a\u200bb \u00ffc") }

// Invalid UTF-8: a lone 0xFF and a TRUNCATED three-byte space prefix
// (0xE2 0x80 at end of string). Real Fields decodes these as
// RuneError (not white space) and keeps them field content,
// byte-preserved; the shim's byte scan must agree.
func fcInvalidUTF8() (uint64, string) { return fieldsJoin("\xffa b\xe2\x80") }

func main() {
	c, j := fcLeadTrail()
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		c, uint64(len(j)),
	)
}
