package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H14: the unicode predicates and case mappings at ASCII (the properties table), Latin-1, the BMP (is16), the
// astral planes (is32), the case-delta and orbit shapes, To with every case and an invalid one, In / Is / IsOneOf.
import (
	"strconv"
	"unicode"
)

func preds(r rune) string {
	b := func(v bool) string {
		if v {
			return "1"
		}
		return "0"
	}
	return b(unicode.IsDigit(r)) + b(unicode.IsLetter(r)) + b(unicode.IsUpper(r)) + b(unicode.IsLower(r)) + b(unicode.IsTitle(r)) + b(unicode.IsPunct(r)) + b(unicode.IsNumber(r)) + b(unicode.IsControl(r)) + b(unicode.IsPrint(r)) + b(unicode.IsGraphic(r)) + b(unicode.IsSymbol(r)) + b(unicode.IsMark(r)) + b(unicode.IsSpace(r))
}
func predicatesAscii() string {
	out := ""
	for _, r := range []rune{'a', 'Z', '0', ' ', '\t', '!', '+', 0x7f, 0, '_', '$'} {
		out += preds(r) + ";"
	}
	return out
}
func predicatesLatin1Bmp() string {
	out := ""
	for _, r := range []rune{'\u00e9', '\u00c9', '\u00b2', '\u00bf', '\u0301', '\u20ac', '\u01c5', '\u00a0', '\u0085', '\u3000', '\u4e00', '\u0660', '\u2028', '\uffff', '\u00ad'} {
		out += preds(r) + ";"
	}
	return out
}
func predicatesAstral() string {
	out := ""
	for _, r := range []rune{0x1d400, 0x1f600, 0x1d7d8, 0x10000, 0x1f1e6, 0xe0001, 0x10ffff, 0x110000, -1} {
		out += preds(r) + ";"
	}
	return out
}
func caseMapping() string {
	out := ""
	for _, r := range []rune{'a', 'A', '\u00e9', '\u00df', '\u01c6', '\u01c4', '\u01c5', '\u017f', '\u212a', '\u2126', '\u03c2', '\u0130', '1', 0x10428, 0x10400, -1, 0x110000} {
		out += strconv.Itoa(int(unicode.ToUpper(r))) + "/" + strconv.Itoa(int(unicode.ToLower(r))) + "/" + strconv.Itoa(int(unicode.ToTitle(r))) + ";"
	}
	return out
}
func simpleFoldOrbits() string {
	out := ""
	for _, r := range []rune{'A', 'a', 'k', 'K', '\u212a', '\u00df', '\u1e9e', '1', '\u03c3', '\u03c2', '\u03a3', '\u01c4', '\u01c5', '\u01c6', -1, 0x10ffff} {
		out += strconv.Itoa(int(unicode.SimpleFold(r))) + ";"
	}
	return out
}
func toCases() string {
	return strconv.Itoa(int(unicode.To(unicode.UpperCase, 'a'))) + "," + strconv.Itoa(int(unicode.To(unicode.LowerCase, 'A'))) + "," + strconv.Itoa(int(unicode.To(unicode.TitleCase, '\u01c6'))) + "," + strconv.Itoa(int(unicode.To(99, 'a'))) + "," + strconv.Itoa(int(unicode.To(-1, 'a'))) + "," + strconv.Itoa(int(unicode.To(unicode.UpperCase, '\u00e9')))
}
func tablesInIs() string {
	b := strconv.FormatBool
	return b(unicode.In('a', unicode.Latin, unicode.Greek)) + b(unicode.In('\u03b1', unicode.Latin)) + b(unicode.In('\u03b1', unicode.Latin, unicode.Greek)) + b(unicode.Is(unicode.Han, '\u65e5')) + b(unicode.Is(unicode.Han, 'a')) + b(unicode.IsOneOf([]*unicode.RangeTable{unicode.Greek, unicode.Cyrillic}, '\u0436')) + b(unicode.Is(unicode.Letter, 0x1d400)) + b(unicode.Is(unicode.Nd, '\u0660')) + b(unicode.In('x'))
}

func main() {
	predicatesAscii()
	predicatesLatin1Bmp()
	predicatesAstral()
	caseMapping()
	simpleFoldOrbits()
	toCases()
	tablesInIs()
}
