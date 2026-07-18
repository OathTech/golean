package main

// The conversions quorum uses between a defined integer type and its
// underlying type in both directions, plus a narrowing conversion of
// MaxUint64 (mirrors uint64(idx) / Index(srt[pos]) / uint8 arithmetic).

type Index uint64

func definedUnderlyingConversion() int {
	var idx Index = 42
	u := uint64(idx)     // defined -> underlying
	back := Index(u + 1) // underlying -> defined
	var big Index = Index(^uint64(0))
	trunc := uint8(big) // narrowing MaxUint64 keeps the low 8 bits (255)
	return int(back) + int(u) + int(trunc)
}
