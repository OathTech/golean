package main

import "fmt"

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// every literal POSITION the emitter lowers (switch case, map literal, struct
// literal, array and slice literal, a package-level initializer and constant,
// a generic instantiation, the fmt desugar's format pieces).

var gInv = "\xff" + "é"
var gNul = "a\x00b"

const gConst = "\xed\xa0\x80"

type S struct {
	A string
	B int
}

type T string

func idT[X ~string](x X) X { return x }

func posSwitch() (int, int) {
	s := "\xff"
	r := 0
	switch s {
	case "\xfe":
		r = 1
	case "\xff":
		r = 2
	case "ÿ":
		r = 3
	}
	t := "\xc3\xbf"
	q := 0
	switch t {
	case "\xff":
		q = 1
	case "ÿ":
		q = 2
	}
	return r, q
}

func posMapLiteral() (int, int, int, int, int) {
	m := map[string]int{"\xff": 1, "ÿ": 2, "a\x00b": 3, "ab": 4, "\xed\xa0\x80": 5}
	return len(m), m["\xff"], m["a\x00b"], m["ab"], m[gConst]
}

func posStructArraySlice() (string, int, string, string, int) {
	v := S{A: "\xff\x00é", B: 1}
	arr := [2]string{"\x80", "😀"}
	sl := []string{"\xc0\x80", " "}
	return v.A, len(v.A), arr[0] + arr[1], sl[0] + sl[1], len(sl[0]) + len(sl[1])
}

func posGlobals() (string, int, string, int, string, int) {
	return gInv, len(gInv), gNul, len(gNul), gConst, len(gConst)
}

func posGeneric() (string, int, string) {
	a := idT("\xff\x00")
	b := idT(T("é\xbf"))
	return a, len(a), string(b)
}

func posFmtFormatPieces() (string, int) {
	s := fmt.Sprintf("a\xff%d\x00%s|é", 7, "\xfe")
	return s, len(s)
}

func main() {
	posSwitch()
}

type keyT string

func bump(n *int) int { *n++; return *n }

// A string constant as a select SEND value, in an unseq multi-target assignment
// beside a call, and as a defined-string map-literal key.
func posSelectUnseqDefinedKey() (string, string, int, int, int) {
	ch := make(chan string, 1)
	select {
	case ch <- "\xff\x00é":
	}
	got := <-ch
	n := 0
	var a string
	var b int
	a, b = "\xed\xa0\x80", bump(&n)
	m := map[keyT]int{keyT("\xff"): 1, "ÿ": 2, keyT(string([]byte{0xff})): 3}
	return got, a, b, len(m), m["\xff"]
}
