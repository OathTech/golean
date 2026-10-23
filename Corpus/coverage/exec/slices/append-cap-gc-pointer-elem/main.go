package main

// The append-spill envelope at the raft-proofs customer's point (G18,
// 2026-10-23): a []*T of capacity 64 appended one element, newLen 65 —
// raft's MemoryStorage.ents shape at its 65th entry. gc realizes 143:
// nextslicecap 128, 128·8 = 1024 > 512 bytes so the malloc header applies,
// class 1152 − 8 = 1144 / 8 (runtime/slice.go growslice, msize.go
// roundupsize @ go1.26.5) — slot 0 of the default tape since G18 (the
// growth formula alone gave 128). The envelope [65, max(32, 2·128) = 256]
// is UNCHANGED (every pre-G18 tape stays valid); members=192 pins its
// cardinality. newLen 65 exceeds the compiler's 32-byte stack buffer
// (4 pointers), so gc takes the heap path even for this local.
// Membership (version-tracking): the strict lane cannot observe a spill's
// capacity (it varies with the tape by design); the machine-level default
// is pinned by the eval tests and by `appendSpillCapAt_zero`.
type entry struct{ index, term uint64 }

func appendCapGcPointerElem() int {
	s := make([]*entry, 64, 64)
	s = append(s, &entry{})
	return cap(s)
}
