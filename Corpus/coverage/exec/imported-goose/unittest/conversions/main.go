// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/conversions.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type stringWrapper string

func typedLiteral() uint64 {
	return 3
}

func literalCast() uint64 {
	// produces a uint64 -> uint64 conversion
	x := uint64(2)
	return x + 2
}

func castInt(p []byte) uint64 {
	return uint64(len(p))
}

func stringToByteSlice(s string) []byte {
	// must be lifted, impure operation
	p := []byte(s)
	return p
}

func byteSliceToString(p []byte) string {
	// must be lifted, impure operation
	s := string(p)
	return s
}

func stringToStringWrapper(s string) stringWrapper {
	return stringWrapper(s)
}

func stringWrapperToString(s stringWrapper) string {
	return string(s)
}

type Uint32 uint32

func testU32NewtypeLen() bool {
	s := make([]byte, 20)
	return Uint32(len(s)) == Uint32(20)
}

type numWrapper int

func (n *numWrapper) inc() {
	*n++
}

func testNumWrapper() {
	n := numWrapper(0)
	n.inc()
}

type withInterface struct {
	a any
}

func testConversionLiteral() bool {
	s := withInterface{nil}
	s = withInterface{a: nil}
	m := map[any]any{nil: nil}
	m[nil] = s
	m[s] = nil
	return m[m[s]] == s
}

// --- GoLean harness ---
// Authored wrapper.

func goleanConversions() int {
	sum := int(typedLiteral()) + int(literalCast())*10
	p := stringToByteSlice("conv")
	sum += int(castInt(p)) * 100
	sum += len(byteSliceToString(p)) * 1000
	sum += len(stringWrapperToString(stringToStringWrapper("wrap"))) * 10000
	testNumWrapper()
	return sum
}


func goleanTestU32NewtypeLen() int {
	if testU32NewtypeLen() {
		return 1
	}
	return 0
}

func goleanTestConversionLiteral() int {
	if testConversionLiteral() {
		return 1
	}
	return 0
}

func main() {}
