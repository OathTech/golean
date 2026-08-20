package main

// strings.Join conformance pins (raft W4.1 item 4 — H-17/G-9, the
// newRaft site's shape). The oracle runs the real strings.Join; the
// machine runs the E5 shim (stdlibshim.go, goleanShimStringsJoin) —
// plain concatenation, byte-identical to upstream's Builder-based
// implementation by construction (same elements, same separators, in
// order).

import "strings"

func joinBasic() string {
	return strings.Join([]string{"a", "bc", "d"}, ",")
}

func joinEmptySlice() (int, string) {
	var nilElems []string
	s1 := strings.Join([]string{}, ",")
	s2 := strings.Join(nilElems, ",")
	return len(s1) + len(s2), s1 + "|" + s2
}

func joinSingle() string {
	return strings.Join([]string{"only"}, ", ")
}

func joinEmptySep() string {
	return strings.Join([]string{"x", "y", "z"}, "")
}

// The newRaft shape: rendered ids joined with "," (raft.go:496).
func joinNewRaftShape() string {
	ids := []uint64{1, 258}
	strs := []string{}
	for _, id := range ids {
		strs = append(strs, hex(id))
	}
	return "[" + strings.Join(strs, ",") + "]"
}

func hex(v uint64) string {
	if v == 0 {
		return "0"
	}
	digits := ""
	for v > 0 {
		digits = string([]byte{"0123456789abcdef"[v&0xf]}) + digits
		v >>= 4
	}
	return digits
}

func main() {
	n, s := joinEmptySlice()
	println(joinBasic(), n, s, joinSingle(), joinEmptySep(), joinNewRaftShape())
}
