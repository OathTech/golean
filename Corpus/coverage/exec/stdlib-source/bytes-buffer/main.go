package main

// bytes.Buffer through the REAL upstream body (stdlib source-through slice
// 2, 2026-09-03; the six-member E5-T shadow model RETIRED). Pure Go: the
// growth idiom `append([]byte(nil), make([]byte, c)...)` in growSlice is the
// same one the Builder overlay uses. Rows cover the write side the model
// had, and the members that were declaration-only stubs under it: the
// read side that does NOT report io.EOF (Next, Bytes, Truncate,
// UnreadByte's error path, Available), Grow's contract and its negative-
// count panic, WriteRune, Cap/Len after Reset, the nil-receiver String()
// special case, and Truncate's out-of-range panic. The io.EOF-reporting
// readers (Read, ReadByte, ReadRune, ReadBytes, ReadString) refuse by name
// — frontier row stdlib-source/frontier/buffer-readbyte-io.

import "bytes"

func bufWriteSide() (string, int) {
	var b bytes.Buffer
	b.WriteString("ab")
	b.WriteByte('c')
	b.Write([]byte("de"))
	n, _ := b.WriteRune('é')
	m, _ := b.WriteRune('😀')
	return b.String(), b.Len()*100 + n*10 + m
}

func bufNextBytesTruncate() (string, string, string, int) {
	var b bytes.Buffer
	b.WriteString("hello world")
	head := string(b.Next(6))
	rest := string(b.Bytes())
	b.Truncate(3)
	return head, rest, b.String(), b.Len()
}

func bufUnreadByteError() (string, bool) {
	var b bytes.Buffer
	b.WriteString("x")
	err := b.UnreadByte() // no prior successful read
	return err.Error(), err != nil
}

func bufGrowContract() string {
	out := ""
	for _, n := range []int{0, 1, 63, 64, 65, 500} {
		var b bytes.Buffer
		b.WriteString("seed")
		b.Grow(n)
		if b.Cap()-b.Len() >= n && b.Available() >= n && b.String() == "seed" {
			out += "y"
		} else {
			out += "N"
		}
	}
	return out
}

func bufGrowNegative() int {
	var b bytes.Buffer
	b.Grow(-5)
	return b.Len()
}

func bufTruncateOutOfRange() int {
	var b bytes.Buffer
	b.WriteString("abc")
	b.Truncate(7)
	return b.Len()
}

func bufResetReuse() (int, string, bool) {
	var b bytes.Buffer
	b.WriteString("first")
	c := b.Cap()
	b.Reset()
	b.WriteString("second!")
	return b.Len(), b.String(), b.Cap() >= c
}

func bufNilReceiverString() string {
	var p *bytes.Buffer
	return p.String()
}

func bufAvailableBuffer() (string, int) {
	var b bytes.Buffer
	b.Grow(16)
	ab := b.AvailableBuffer()
	ab = append(ab, "xyz"...)
	b.Write(ab)
	return b.String(), len(ab)
}

// (bytes.ToUpper/ToLower/Join/Repeat reach bytealg.MakeNoZero — body-less,
// NOT overlaid at those four sites; they refuse by name — frontier row
// stdlib-source/frontier/bytes-toupper-makenozero.)
func bytesOthers() (bool, bool, int, int, string, string, bool) {
	a := []byte("Hello, World")
	return bytes.Equal(a, []byte("Hello, World")), bytes.Equal(nil, []byte{}), bytes.Compare([]byte("a"), []byte("b")),
		bytes.Index(a, []byte("World")), string(bytes.TrimPrefix(a, []byte("Hello, "))), string(bytes.TrimSpace([]byte("  x y  "))), bytes.HasPrefix(a, []byte("Hell"))
}

func main() {
	s, n := bufWriteSide()
	println(s, n)
	h, r, t, l := bufNextBytesTruncate()
	println(h, r, t, l)
	e, ok := bufUnreadByteError()
	println(e, ok)
	println(bufGrowContract())
	rl, rs, rc := bufResetReuse()
	println(rl, rs, rc)
	println(bufNilReceiverString())
	as, al := bufAvailableBuffer()
	println(as, al)
	o1, o2, o3, o4, o5, o6, o7 := bytesOthers()
	println(o1, o2, o3, o4, o5, o6, o7)
}
