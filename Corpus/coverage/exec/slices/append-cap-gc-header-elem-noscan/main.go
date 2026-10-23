package main

// The noscan twin of append-cap-gc-header-elem (G18, 2026-10-23): a
// []bigNoscan (1024 bytes, no pointers) of capacity 4 appended one
// element: nextslicecap 8, 8·1024 = 8192 is a size class and a pointer-free
// backing carries no malloc header → cap 8 (the pointerful twin gets 9).
// Slot 0 since G18. Envelope [5, 32], bound 28; members=28. Membership
// (version-tracking).
type bigNoscan struct {
	pad [1024]byte
}

func appendCapGcHeaderElemNoscan() int {
	s := make([]bigNoscan, 4, 4)
	s = append(s, bigNoscan{})
	return cap(s)
}
