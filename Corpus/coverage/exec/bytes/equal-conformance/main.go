package main

// bytes.Equal conformance pins (raft W4.1 item 4 — H-13/G-7, the
// (*raft).Step site's shape). The oracle runs the real bytes.Equal;
// the machine runs the E5 shim (goleanShimBytesEqual). The documented
// contract pinned here: same length + same bytes, and "a nil argument
// is equivalent to an empty slice" — nil==empty is TRUE, which an
// identity-based or nil-strict shim would get wrong.

import "bytes"

func bytesEqualBasic() int {
	n := 0
	if bytes.Equal([]byte("abc"), []byte("abc")) {
		n += 1
	}
	if !bytes.Equal([]byte("abc"), []byte("abd")) {
		n += 2
	}
	if !bytes.Equal([]byte("abc"), []byte("ab")) {
		n += 4
	}
	return n
}

func bytesEqualNilEmpty() int {
	var nilB []byte
	n := 0
	if bytes.Equal(nilB, []byte{}) {
		n += 1
	}
	if bytes.Equal(nilB, nilB) {
		n += 2
	}
	if bytes.Equal([]byte{}, []byte{}) {
		n += 4
	}
	if !bytes.Equal(nilB, []byte{0}) {
		n += 8
	}
	return n
}

// The (*raft).Step shape (raft.go:1102): comparing message context
// bytes against a computed value.
func bytesEqualStepShape() int {
	ctx := []byte("ctx-7")
	same := []byte("ctx-")
	same = append(same, '7')
	if bytes.Equal(ctx, same) {
		return 1
	}
	return 0
}

func main() {
	println(bytesEqualBasic(), bytesEqualNilEmpty(), bytesEqualStepShape())
}
