package main

// E4STRB (Stage E audit fix round F4, 2026-09-21): `string(b)` READS b's backing array at the
// conversion — an occurrence of its own. b is private but aliased by c, which m writes:
// `println(string(b) + m())` → {ab, zb}; gc draws zb (the conversion after the call —
// OBYTES2STR is not in order.go's call class). The first E4 cut classified the sweep as
// all-forced (a conversion «pure over its operand's value») and sent it to the legacy path,
// which realizes gc's zb alone — a pin presented as forced. Reference enumerate.py E4h.
func e4strb() {
	b := []byte("ab")
	c := b
	m := func() string { c[0] = 'z'; return "" }
	println(string(b) + m())
}

func main() { e4strb() }
