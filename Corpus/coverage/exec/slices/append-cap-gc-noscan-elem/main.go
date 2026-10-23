package main

// The noscan twin of append-cap-gc-pointer-elem (G18, 2026-10-23): a []int
// of capacity 64 appended one element, newLen 65. The 1024-byte backing of
// a pointer-free element carries no malloc header, so gc realizes the
// class 1024 / 8 = 128 (where []*T gets 143) — slot 0 of the default tape
// since G18. Same envelope [65, 256], same bound 192; members=192.
// Membership (version-tracking), as the pointer row.
func appendCapGcNoscanElem() int {
	s := make([]int, 64, 64)
	s = append(s, 1)
	return cap(s)
}
