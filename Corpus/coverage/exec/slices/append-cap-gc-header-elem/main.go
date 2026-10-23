package main

// gc's malloc header made visible on a LARGE pointerful element (G18,
// 2026-10-23): the header is charged when the pointerful backing exceeds
// 512 bytes (runtime/msize.go roundupsize: !noscan && size >
// MinSizeForMallocHeader). A []bigPtr (1024 bytes, one pointer field) of
// capacity 4 appended one element: nextslicecap 8, 8·1024 + 8 = 8200 →
// class 9472 − 8 = 9464 / 1024 → cap 9, where the noscan twin
// (append-cap-gc-header-elem-noscan) stays at the class 8192 → 8. Slot 0
// since G18. Envelope [5, max(32, 2·8) = 32], bound 28; members=28. A
// 1024-byte element never fits the 32-byte stack buffer, so gc takes the
// heap path. Membership (version-tracking).
type bigPtr struct {
	p   *int
	pad [1016]byte
}

func appendCapGcHeaderElem() int {
	s := make([]bigPtr, 4, 4)
	s = append(s, bigPtr{})
	return cap(s)
}
