package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md; the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Group A5: a string observes as its bytes; a NUL and a DEL byte travel as bytes, a 4 KiB string in full.

type S string

func emptyAndASCII() (string, string, [2]string) { return "", "abc", [2]string{"", "x y"} }
func multibyte() (string, string)                { return "héllo", "日本語" }
func nulAndDel() (string, string)                { return "a\x00b", "\x7f" }
func fourKiB() (string, int) {
	s := ""
	for i := 0; i < 256; i++ {
		s += "0123456789abcdef"
	}
	return s, len(s)
}
func definedStringKind() (S, [1]S) { return S("s"), [1]S{"t"} }

func main() {
	emptyAndASCII()
	multibyte()
	nulAndDel()
	fourKiB()
	definedStringKind()
}
