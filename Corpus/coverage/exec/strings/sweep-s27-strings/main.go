package main

import (
	"strings"
	"unicode"
	"unicode/utf8"
)

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The `strings` package (source-through) over invalid, NUL, control and
// multi-byte classes — every function that decodes runes has a byte-level
// answer gc fixes: byte-wise search with partial needles, Count/Repeat/Replace,
// the case mappings (an invalid byte maps to U+FFFD), ToValidUTF8, Trim with an
// ASCII cutset and TrimFunc, Split/Cut/Join with invalid separators, EqualFold
// and Fields, the Builder's invalid writes, the unicode predicates at the
// sentinel. The calls that reach strings.IndexRune (Trim with a non-ASCII
// cutset, IndexAny/ContainsAny, IndexRune/ContainsRune) are refused by name at
// the frontend («goto target label fallback not at function body top level»)
// and are recorded as coverage gaps on the entries, not rowed.

func searchWithPartialNeedles() (int, bool, bool, bool, int, int, int) {
	s := "aé日\xffz"
	return strings.Index(s, "\xa9"), strings.Contains(s, "\xe6\x97"), strings.HasPrefix("é", "\xc3"), strings.HasSuffix("日", "\xa5"), strings.IndexByte(s, 0xff), strings.LastIndex(s, "\xff"), strings.Index(s, "\x00")
}

func countRepeatReplace() (int, int, int, string, string, string) {
	return strings.Count("\xff\xff", ""), strings.Count("é\xa9", "\xa9"), strings.Count("", ""), strings.Repeat("\xff\x00", 3), strings.Replace("a\xffb\xffc", "\xff", "<�>", -1), strings.ReplaceAll("\xc0\x80", "\x80", "_")
}

func caseMapping() (string, string, string, string, string, string) {
	return strings.ToUpper("a\xffb\x00c"), strings.ToLower("É\xed\xa0\x80\x7f"), strings.ToUpper("x\uFEFFy\u0085"), strings.Map(func(r rune) rune { return r + 1 }, "a\xffé"), strings.Map(func(r rune) rune {
		if r == utf8.RuneError {
			return -1
		}
		return r
	}, "a\xffb\xef\xbf\xbdc"), strings.ToUpper("ascii only")
}

func toValidUTF8() (string, string, string, string) {
	return strings.ToValidUTF8("a\xffb\xe2\x82c", "?"), strings.ToValidUTF8("\xc0\x80\xed\xa0\x80", ""), strings.ToValidUTF8("ok\xef\xbf\xbd", "!"), strings.ToValidUTF8("\xf4\x90\x80\x80\xff", "<�>")
}

func trimAsciiCutsetAndFunc() (string, string, string, string) {
	return strings.TrimLeft("\x00\x00a\x00", "\x00"), strings.Trim("\x7fa\x7f", "\x7f"), strings.TrimFunc("\xffa\xff", func(r rune) bool { return r == utf8.RuneError }), strings.TrimPrefix("\xc3\xa9", "\xc3")
}

func splitCutJoinInvalid() (int, string, string, string, string, bool, string) {
	parts := strings.Split("a\xffb\xffc", "\xff")
	before, after, found := strings.Cut("x\xed\xa0\x80y", "\xa0")
	return len(parts), parts[0] + "|" + parts[1] + "|" + parts[2], strings.Join(parts, "\x00"), before, after, found, strings.Join([]string{"\xff", "\xfe"}, "é")
}

func equalFoldAndFields() (bool, bool, bool, int, int) {
	f := strings.Fields("\u0085a\xffb c")
	return strings.EqualFold("\xff", "\xff"), strings.EqualFold("\xff", "\xef\xbf\xbd"), strings.EqualFold("K", "K"), len(f), len(f[0])
}

func builderInvalidWrites() (string, int, string, int) {
	var b strings.Builder
	b.WriteByte(0xff)
	b.WriteRune(0xD800)
	b.WriteRune(-1)
	b.WriteString("\xe2\x82")
	b.WriteByte(0)
	b.WriteRune(0x1F600)
	s := b.String()
	var c strings.Builder
	n, _ := c.WriteRune(0x110000)
	return s, len(s), c.String(), n
}

func unicodePredicatesOnBytes() (bool, bool, bool, bool, bool, bool) {
	return unicode.IsSpace(utf8.RuneError), unicode.IsSpace(0x85), unicode.IsSpace(0xA0), unicode.IsLetter(utf8.RuneError), unicode.IsPrint(0x7f), unicode.IsPrint(0xFEFF)
}

func main() {
	searchWithPartialNeedles()
}
