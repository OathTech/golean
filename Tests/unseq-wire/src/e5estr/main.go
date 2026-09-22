package main

// E5ESTR (Stage E5, family E5e — strings; lane core/unseq-stage-e5-0922, 2026-09-22): `int(s[i:][0]) + m()`
// with i captured (m: i = 1; returns 5). The substring `s[i:]` is a bounds-checked pure op on the string
// VALUE (spec#Slice_expressions) and its byte `[0]` a second (spec#Index_expressions); both are unordered
// against m (the conversion a pure head, no E1 edge). Before m 'a' → 97 + 5 = 102; after m 'b' → 98 + 5 =
// 103 (gc's). Reference enumerate.py E5e2; {102, 103}.
func e5estr() int {
	s := "ab"
	i := 0
	m := func() int { i = 1; return 5 }
	return int(s[i:][0]) + m()
}

func main() { println(e5estr()) }
