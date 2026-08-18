package main

// spec#Iota block Iota-2-7755546c: within one ConstSpec each iota has the
// same value (bit0, mask0 = 1<<iota, 1<<iota - 1 at iota == 0), the implicit
// repetition of the last expression list re-evaluates with the advancing
// iota, and blank identifiers consume an iota step: bit0 mask0 == 1 0,
// bit1 mask1 == 2 1, bit3 mask3 == 8 7.

const (
	bit0, mask0 = 1 << iota, 1<<iota - 1 // bit0 == 1, mask0 == 0  (iota == 0)
	bit1, mask1                          // bit1 == 2, mask1 == 1  (iota == 1)
	_, _                                 //                        (iota == 2, unused)
	bit3, mask3                          // bit3 == 8, mask3 == 7  (iota == 3)
)

func iotaMultiPair() int {
	if bit0 != 1 || mask0 != 0 {
		return 1
	}
	if bit1 != 2 || mask1 != 1 {
		return 2
	}
	if bit3 != 8 || mask3 != 7 {
		return 3
	}
	return 0
}
