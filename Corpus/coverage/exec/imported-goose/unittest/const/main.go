// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/const.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


const GlobalConstant string = "foo"

const UntypedStringConstant = "bar" // an untyped string

const UntypedInt = 13

const OtherUntypedInt = UntypedInt + UntypedInt

const TypedInt uint64 = 32

const ConstWithArith uint64 = 4 + 3*TypedInt

const TypedInt32 uint32 = 3

const DivisionInConst uint64 = (4096 - 8) / 8

const ModInConst uint64 = 513 + 12%8 // 517

const ModInConstParens uint64 = (513 + 12) % 8 // 5

const SignedIntegerExample int64 = -37

const (
	First = iota
	Second
	Third
)

const (
	ComplicatedFirst uint64 = 2*iota + 3
	ComplicatedSecond
	ComplicatedThird
)

func useUntypedInt() uint64 {
	return UntypedInt + TypedInt
}

func useUntypedString() string {
	return UntypedStringConstant
}

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func goleanConst() int {
	sum := int(useUntypedInt())
	sum += len(useUntypedString())
	sum += len(GlobalConstant)
	sum += OtherUntypedInt
	sum += int(ConstWithArith)
	sum += int(TypedInt32)
	sum += int(DivisionInConst)
	sum += int(ModInConst) + int(ModInConstParens)
	sum += int(SignedIntegerExample)
	sum += First + Second*10 + Third*100
	sum += int(ComplicatedFirst) + int(ComplicatedSecond)*10 + int(ComplicatedThird)*100
	return sum
}

func main() {}
