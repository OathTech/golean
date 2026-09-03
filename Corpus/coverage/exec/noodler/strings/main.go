// noodler probes — strings, runes and the modeled stdlib subset
// (spec#String_types, spec#For_range over strings; shim conformance for
// strings/strconv/fmt/errors per D-002's Fields standard).
package main

import (
	"errors"
	"fmt"
	"strconv"
	"strings"
)

// Range indices over multi-byte runes skip continuation bytes.
func rangeIndicesMultibyte() (int, int) {
	s := "aé€😀"
	idx := 0
	n := 0
	for i := range s {
		idx = idx*10 + i
		n++
	}
	return idx, n*100 + len(s)
}

// Byte indexing inside a multi-byte rune returns the raw byte.
func byteInsideRune() (byte, byte, int) {
	s := "é"
	return s[0], s[1], len(s)
}

// string([]byte) copies: later mutation of the bytes is invisible.
func stringFromBytesCopies() string {
	b := []byte("ab")
	s := string(b)
	b[0] = 'x'
	return s + string(b)
}

// Lexicographic byte comparison, prefix rule, and case.
func stringOrdering() (bool, bool, bool, bool) {
	return "ab" < "abc", "Z" < "a", "" < "a", "b" > "abc"
}

// Concatenation in a loop and += on strings.
func concatLoop() (string, int) {
	s := ""
	for i := 0; i < 5; i++ {
		s += string(rune('a' + i))
	}
	s = s + s[:2]
	return s, len(s)
}

// Rune count vs byte length.
func runeCountVsLen() (int, int) {
	s := "héllo, 世界"
	n := 0
	for range s {
		n++
	}
	return n, len(s)
}

// strings.Fields treats Unicode spaces (NBSP, EM SPACE) as separators.
func fieldsUnicodeSpaces() (int, int, int) {
	return len(strings.Fields("a b c")), len(strings.Fields("   ")), len(strings.Fields(" x "))
}

// strings.TrimSpace strips Unicode spaces.
func trimSpaceUnicode() (string, int) {
	r := strings.TrimSpace("  x\ty  ")
	return r, len(r)
}

// strings.Split edges: separator longer than input, empty input, trailing
// separator.
func splitEdges() (int, int, int, string) {
	a := strings.Split("abc", "abcd")
	b := strings.Split("", ",")
	c := strings.Split("a,b,", ",")
	return len(a), len(b), len(c), c[2] + "|" + c[0]
}

// strings.Join and Repeat edges.
func joinRepeatEdges() (string, string, string) {
	return strings.Join(nil, ","), strings.Join([]string{"a"}, ","), strings.Repeat("ab", 0) + strings.Repeat("-", 3)
}

// strconv.ParseUint: success and the two error texts.
func parseUintEdges() (uint64, string, string, uint64) {
	v, _ := strconv.ParseUint("ff", 16, 8)
	_, e1 := strconv.ParseUint("18446744073709551616", 10, 64)
	_, e2 := strconv.ParseUint("-1", 10, 64)
	w, e3 := strconv.ParseUint("300", 10, 8)
	if e3 == nil {
		return 0, "", "", 0
	}
	return v, e1.Error(), e2.Error(), w
}

// fmt.Sprint spacing: spaces only between non-string operands.
func sprintSpacing() (string, string, string) {
	return fmt.Sprint(1, 2), fmt.Sprint("a", "b"), fmt.Sprint("a", 1, 2, "b")
}

// fmt.Sprintf with the common verbs.
func sprintfVerbs() string {
	return fmt.Sprintf("%d|%s|%v|%q|%t", -3, "s", "v", "q", true)
}

// fmt.Sprintln appends a newline and always spaces.
func sprintlnBasics() (string, int) {
	s := fmt.Sprintln("a", "b", 3)
	return s, len(s)
}

// errors.New and fmt.Errorf produce distinct error values with the same
// text.
func errorsNewAndErrorf() (string, bool, bool) {
	e1 := errors.New("boom")
	e2 := fmt.Errorf("boom")
	return e1.Error() + e2.Error(), e1 == e2, e1 == e1
}

// A Stringer rendered by %v and Sprint.
type Weekday int

func (d Weekday) String() string {
	return [...]string{"Sun", "Mon", "Tue"}[d]
}

func stringerRendering() (string, string) {
	return fmt.Sprintf("%v-%d", Weekday(1), Weekday(1)), fmt.Sprint(Weekday(2))
}

// Comparing strings built differently but byte-equal.
func byteEqualStrings() (bool, bool) {
	a := "héllo"
	b := string([]byte{'h', 0xc3, 0xa9, 'l', 'l', 'o'})
	c := string([]rune{'h', 'é', 'l', 'l', 'o'})
	return a == b, b == c
}

// Substring sharing: slicing a string then converting to bytes copies.
func substringThenBytes() (string, string) {
	s := "hello world"
	sub := s[6:]
	b := []byte(sub)
	b[0] = 'W'
	return sub, string(b)
}

// Invalid UTF-8 survives concatenation and slicing byte-for-byte.
func invalidBytesPreserved() (int, byte, bool) {
	s := "\xff" + "a" + "\xfe"
	t := s[0:1] + s[2:]
	return len(t), t[1], t == "\xff\xfe"
}

func main() {}
