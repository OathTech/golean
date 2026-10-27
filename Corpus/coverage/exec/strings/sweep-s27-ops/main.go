package main

import (
	"slices"
	"strings"
)

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// ordering, map keys, []byte conversions, string(byte) and append over every
// byte class.

func lenPerClass() (int, int, int, int, int, int, int) {
	return len("a\x00b"), len("a\xef\xbb\xbfb"), len("😀"), len("\xe2\x82"), len("\xed\xa0\x80"), len(""), len("\u0085\x7f")
}

func indexPerClass() (byte, byte, byte, byte, byte, byte, byte, byte, byte, byte) {
	s := "\x00\x7f\xc2\x85\xef\xbb\xbf\xf4\x90\xff"
	return s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9]
}

func sliceMidSequence() (string, string, string, bool, int) {
	s := "aé日😀z"
	a := s[1:2]  // the lead byte of é
	b := s[4:6]  // the last two bytes of 日
	c := s[7:10] // three of 😀's four bytes
	back := s[:1] + a + s[2:4] + b + s[6:7] + c + s[10:]
	return a, b, c, back == s, len(back)
}

func concatFormsValid() (bool, bool, string, int) {
	left := "\xc3"
	right := "\xa9"
	joined := left + right
	nul := "a" + "\x00" + "" + "b"
	return joined == "é", nul == "a\x00b", joined, len(nul)
}

func comparePerClass() (bool, bool, bool, bool, bool, bool, bool, bool) {
	return "\x00" > "", "a\x00" > "a", "a\x00" < "a\x01", "\xed\xa0\x80" > "\xed\x9f\xbf", "\xff" > "😀", "é" < "\xc3\xa9\x00", "ab" < "abc", "\xef\xbb\xbf" > "\xef\xbb\xbe"
}

func minMaxSortStrings() (string, string, int, string, string, string, string) {
	lo := min("\xff", "é", "a", "\x00")
	hi := max("\xff", "é", "a", "\x00")
	c := strings.Compare("\xff", "ÿ")
	xs := []string{"\xff", "é", "a\x00", "a", "😀", ""}
	slices.Sort(xs)
	return lo, hi, c, xs[0], xs[1], xs[2], xs[5]
}

type pair struct {
	A string
	B string
}

func boxedAndAggregateEquality() (bool, bool, bool, bool, bool) {
	var x any = "\xff"
	var y any = "\xff"
	var z any = "ÿ"
	p := pair{"\xff\x00", "é"}
	q := pair{"\xff" + "\x00", "\xc3\xa9"}
	arr1 := [2]string{"\x80", "\xed\xa0\x80"}
	arr2 := [2]string{"\x80", "\xed\xa0" + "\x80"}
	arr3 := [2]string{"\x80", "\xed\xa0\x81"}
	return x == y, x == z, p == q, arr1 == arr2, arr1 == arr3
}

func mapKeysNulAndBuilt() (int, int, int, int, bool, int) {
	m := map[string]int{}
	m["ab"] = 1
	m["a\x00b"] = 2
	m[""] = 3
	m["\x00"] = 4
	k := string([]byte{0x61, 0x00, 0x62})
	got := m[k]
	delete(m, k)
	_, still := m["a\x00b"]
	bs := []byte("\xff")
	m[string(bs)] = 9
	return len(m), got, m["ab"], m["\x00"], still, m["\xff"]
}

type key struct {
	S string
	N int
}

func structKeyAndAnyKey() (int, int, int, int) {
	m := map[key]int{}
	m[key{"\xff", 1}] = 1
	m[key{"ÿ", 1}] = 2
	m[key{string([]byte{0xff}), 1}] = 3
	a := map[any]int{}
	a["\xed\xa0\x80"] = 1
	a[string([]byte{0xed, 0xa0, 0x80})] = 2
	a["\xef\xbf\xbd"] = 3
	return len(m), m[key{"\xff", 1}], len(a), a["\xed\xa0\x80"]
}

func bytesFromStringPerClass() (int, byte, byte, byte, byte, byte, int) {
	bs := []byte("\x00\xc0\x80\xed\xa0\x80\xf4\x90\x80\x80")
	cs := []byte("")
	return len(bs), bs[0], bs[1], bs[3], bs[6], bs[9], len(cs)
}

func stringFromBytesPerClass() (string, int, string, string, bool) {
	a := string([]byte{0xef, 0xbb, 0xbf, 0x00, 0x7f})
	b := string([]byte{0xf0, 0x9f, 0x98})
	c := string([]byte{0xc2, 0x85, 0xe2, 0x80, 0xa8})
	return a, len(a), b, c, a == "\uFEFF\x00\x7f"
}

type myByte byte
type myString string
type myBytes []byte

func definedConversionsKeepBytes() (string, int, byte, byte, string) {
	b := []myByte("\xff\x00é")
	s := myString(b)
	mb := myBytes(s)
	t := string(mb)
	return string(s), len(b), byte(b[0]), byte(mb[1]), t
}

func stringOfByteVsSlice() (string, int, string, int, string, string, string) {
	var b byte = 0xff
	var i8 int8 = -1
	var u16 uint16 = 0xFFFD
	var i64 int64 = 0x10FFFF
	return string(rune(b)), len(string(rune(b))), string([]byte{b}), len(string([]byte{b})), string(rune(i8)), string(rune(u16)), string(rune(i64))
}

// The DIRECT integer-kind conversions (`string(b)` for a byte, an int8, a
// uint64): the emitter's `string-from-rune` applies to every integer kind
// (vet warns, gc compiles and runs them).
func stringOfIntKindsDirect() (string, int, string, string, string, string) {
	var b byte = 0xff
	var i8 int8 = -1
	var u64 uint64 = 1 << 40
	var i int = 0x1F600
	var u8 uint8 = 0x7f
	return string(b), len(string(b)), string(i8), string(u64), string(i), string(u8)
}

func appendStringToBytes() (int, byte, byte, byte, string) {
	bs := []byte{0x41}
	bs = append(bs, "\xff\x00é"...)
	return len(bs), bs[1], bs[2], bs[3], string(bs)
}

func main() {
	lenPerClass()
}
