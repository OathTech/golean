// spec#Conversions_to_and_from_a_string_type block Conversions_to_and_from_a_string_type-4-e4dd55f2
// String → rune-slice conversions with the spec's own code-point
// assertions: []rune(myString("白鵬翔")) == {0x767d, 0x9d6c, 0x7fd4},
// []rune("") == []rune{}, the defined slice type runes,
// []myRune("♫♬") == {0x266b, 0x266c}, and
// []myRune(myString("🌐")) == {0x1f310}. Each spec-asserted code
// point is load-bearing in a score bit.
package main

type runes []rune
type myRune rune
type myString string

func stringToRunes() int {
	score := 0
	r := []rune(myString("白鵬翔")) // []rune{0x767d, 0x9d6c, 0x7fd4}
	if len(r) == 3 && r[0] == 0x767d && r[1] == 0x9d6c && r[2] == 0x7fd4 {
		score += 1
	}
	e := []rune("") // []rune{}
	if len(e) == 0 {
		score += 2
	}
	rr := runes("白鵬翔") // []rune{0x767d, 0x9d6c, 0x7fd4}
	if len(rr) == 3 && rr[0] == 0x767d && rr[1] == 0x9d6c && rr[2] == 0x7fd4 {
		score += 4
	}
	m := []myRune("♫♬") // []myRune{0x266b, 0x266c}
	if len(m) == 2 && m[0] == 0x266b && m[1] == 0x266c {
		score += 8
	}
	g := []myRune(myString("🌐")) // []myRune{0x1f310}
	if len(g) == 1 && g[0] == 0x1f310 {
		score += 16
	}
	return score
}

func main() {
	stringToRunes()
}
