// R3 probe: cap of []byte(s) across escape regimes and lengths.
// The machine's singleton is cap = len; gc's escaping path is
// recorded realizing roundupsize(len).
package main

var sink []byte

func main() {
	// non-escaping, len 5
	b5 := []byte("hello")
	println("local    len", len(b5), "cap", cap(b5))
	// escaping, len 5
	sink = []byte("hello")
	println("escaping len", len(sink), "cap", cap(sink))

	s33 := "abcdefghijklmnopqrstuvwxyzabcdefg" // len 33
	b33 := []byte(s33)
	println("local    len", len(b33), "cap", cap(b33))
	sink = []byte(s33)
	println("escaping len", len(sink), "cap", cap(sink))

	s100 := ""
	for i := 0; i < 10; i++ {
		s100 += "0123456789"
	}
	b100 := []byte(s100)
	println("local    len", len(b100), "cap", cap(b100))
	sink = []byte(s100)
	println("escaping len", len(sink), "cap", cap(sink))
}
