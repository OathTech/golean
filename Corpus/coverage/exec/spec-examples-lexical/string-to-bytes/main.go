// spec#Conversions_to_and_from_a_string_type block Conversions_to_and_from_a_string_type-3-5710b646
// String → byte-slice conversions with the spec's own byte-level value
// assertions: []byte("hellø") == {'h','e','l','l','\xc3','\xb8'},
// []byte("") == []byte{} (the prose asserts a NON-NIL slice), the
// defined slice type bytes, []myByte("world!"), and
// []myByte(myString("🌏")) == {'\xf0','\x9f','\x8c','\x8f'}. Each
// spec-asserted byte is load-bearing in a score bit.
package main

type bytes []byte
type myByte byte
type myString string

func stringToBytes() int {
	score := 0
	b := []byte("hellø") // []byte{'h', 'e', 'l', 'l', '\xc3', '\xb8'}
	if len(b) == 6 && b[0] == 'h' && b[1] == 'e' && b[2] == 'l' && b[3] == 'l' && b[4] == '\xc3' && b[5] == '\xb8' {
		score += 1
	}
	e := []byte("") // []byte{}
	if len(e) == 0 && e != nil {
		score += 2
	}
	bb := bytes("hellø") // []byte{'h', 'e', 'l', 'l', '\xc3', '\xb8'}
	if len(bb) == 6 && bb[0] == 'h' && bb[4] == '\xc3' && bb[5] == '\xb8' {
		score += 4
	}
	w := []myByte("world!") // []myByte{'w', 'o', 'r', 'l', 'd', '!'}
	if len(w) == 6 && w[0] == 'w' && w[1] == 'o' && w[2] == 'r' && w[3] == 'l' && w[4] == 'd' && w[5] == '!' {
		score += 8
	}
	g := []myByte(myString("🌏")) // []myByte{'\xf0', '\x9f', '\x8c', '\x8f'}
	if len(g) == 4 && g[0] == '\xf0' && g[1] == '\x9f' && g[2] == '\x8c' && g[3] == '\x8f' {
		score += 16
	}
	return score
}

func main() {
	stringToBytes()
}
