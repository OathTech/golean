// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/enum.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type Enum1 uint64

const (
	Enum1A Enum1 = iota
	Enum1B
	Enum1C
)

type Enum2 int

const (
	Enum2A         Enum2 = 1    // line comment 1
	Enum2B, Enum2C       = 3, 4 // line comment 2
	Enum2D         Enum2 = 15   // line comment 3
)

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func goleanEnum() int {
	return int(Enum1A) + int(Enum1B)*2 + int(Enum1C)*3 +
		int(Enum2A)*10 + int(Enum2B)*100 + int(Enum2C)*1000 + int(Enum2D)*10000
}

func main() {}
