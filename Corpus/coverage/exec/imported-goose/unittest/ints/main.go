// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/ints.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func useInts(x uint64, y uint32) (uint64, uint32) {
	var z uint64
	z = uint64(y)
	z = z + 1
	var y2 uint32
	y2 = y + 3
	return z, y2
}

func signedMidpoint(x int, y int) int {
	return (x + y) / 2
}

type my_u32 uint32

type also_u32 my_u32

const ConstWithAbbrevType also_u32 = 3

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func goleanInts() int {
	z, y2 := useInts(7, 3)
	return int(z)*1000 + int(y2)*100 + signedMidpoint(3, 5)*10 + int(ConstWithAbbrevType)
}

func main() {}
