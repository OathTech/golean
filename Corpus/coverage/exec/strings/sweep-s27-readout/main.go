package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// machine's `goValueJson` bytes array against the harness's reflect String arm,
// nested in a struct, an array and an interface, and at a defined string type.

func returnNulDelC1() string          { return "a\x00b\x7fc\u0085\u0080" }
func returnBomAndLineSeps() string    { return "\uFEFFx  " }
func returnJsonSensitive() string     { return "\"\\/<>&'\x1f\x08\x0c" }
func returnFourByte() string          { return "😀\U0010FFFF" }
func returnSurrogateOverlong() string { return "\xed\xa0\x80\xc0\x80\xf4\x90\x80\x80\xfe\xff" }
func returnEmpty() (string, int)      { return "", len("") }

func returnLong300() (string, int) {
	s := ""
	for i := 0; i < 100; i++ {
		s += "é\xff"
	}
	return s, len(s)
}

func returnLong10k() (int, byte, byte, string) {
	s := ""
	for i := 0; i < 1024; i++ {
		s += "0123456789"
	}
	return len(s), s[0], s[10239], s[10230:]
}

type defined string

func returnDefinedAndMixed() (defined, int, string, bool, string) {
	return defined("\xff\x00é"), 3, "😀", true, "\xc0\x80"
}

type holder struct {
	Name  string
	Tag   defined
	Pair  [2]string
	Count int
}

func returnStructWithStrings() holder {
	return holder{Name: "\xff\x00", Tag: defined("é\x7f"), Pair: [2]string{"\xed\xa0\x80", "😀"}, Count: 2}
}

func returnArrayOfStrings() [3]string {
	return [3]string{"\x00", "\xff", "\uFEFF"}
}

func returnInterfaceStrings() (any, any, any) {
	return "\xff\x00", defined("é\xbf"), any("")
}

func main() {
	returnNulDelC1()
}
