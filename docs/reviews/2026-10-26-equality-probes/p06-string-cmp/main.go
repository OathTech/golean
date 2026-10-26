package main

func main() { run() }

func run() {
	println("a" < "b", "ab" < "b", "Z" < "a", "" < "a", "a" < "", "a" == "a", "a" != "b")
	println("é" > "z", "é" < "z", "\xff" > "z", "\x00" < "a", "a\x00" > "a", "a\x00" == "a")
	b := []byte{0xff, 0xfe}
	s := string(b)
	println(s == "\xff\xfe", s > "\xff", len(s) == 2, s < "\xff\xff")
	println(string(rune(-1)) == "�", string(rune(0x110000)) == "�", string(rune(0xD800)) == "�", string(rune(0x41)) == "A")
	t := "hello world"
	println(t[0:5] == "hello", t[6:] == "world", t[0:0] == "", t[:1] < t[1:2])
	u := "héllo"
	println(len(u) == 6, u[1] == 0xc3, u[1:3] == "é", []byte(u)[2] == 0xa9)
	c := "ab" + "c"
	println(c == "abc", c >= "abc", c <= "abc", c > "abb", c < "abd")
	var e string
	println(e == "", e < "a", e <= "", e >= "")
	type MyStr string
	var ms MyStr = "x"
	println(ms == "x", ms < "y", MyStr("x") == ms, string(ms) == "x")
	// runes compare numerically
	println('a' < 'b', 'é' > 'z', rune(0x10FFFF) > 'a')
	// comparing strings built from runes
	r := []rune{0x10FFFF, 0x41}
	println(string(r) == "\U0010FFFFA", string(r) > "A", string(r[1:]) == "A")
	// switch on string
	switch s2 := "b" + ""; s2 {
	case "a":
		println("a")
	case "b":
		println("b")
	default:
		println("d")
	}
}
