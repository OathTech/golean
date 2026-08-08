// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/type_alias.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type my_u64 = uint64

type Timestamp uint64

type UseTypeAbbrev my_u64

type UseNamedType Timestamp

func convertToAlias() Timestamp {
	x := uint64(2)
	return Timestamp(x)
}

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func goleanTypeAlias() int {
	t := convertToAlias()
	u := UseTypeAbbrev(5)
	v := UseNamedType(7)
	return int(t)*100 + int(u)*10 + int(v)
}

func main() {}
