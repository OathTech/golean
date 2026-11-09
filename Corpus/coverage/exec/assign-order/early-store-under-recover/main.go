package main

// BUG-432 (the divergence ledger's L-016; the latitude inventory's E5): gc
// stores an EARLIER target of a multi-target assignment before a LATER
// right-hand operand's panic when that operand reads no memory — a division
// or a shift whose operands are locals — and the early store is visible
// after `recover`. spec#Assignment_statements orders the assignment in two
// phases (every operand first, every store after), so no store happens when
// a phase-1 operand panics; the machine holds the spec's answer. gc holds it
// back only when the later operand reads memory (an index, a global, a
// failing type assertion). Each subject sets the earlier target to 58, panics
// in the later operand, recovers, and returns the target: 58 is the spec's
// answer on every cell; gc returns 29 on the cells whose later operand reads
// no memory (`-gcflags=all=-N -l` agrees with the default build — the
// ledger's measurement: the deviation is in `walk`, not the optimizer).

var gA uint64 = 58
var gB uint64 = 58
var zG int16 = 0
var zH int16 = 1

type l016T struct{ x uint64 }

// A local target, a local divisor: gc 29 (the early store), spec 58.
func l016LocalDivisor() (r uint64) {
	v := uint64(58)
	z := int16(0)
	var b int16
	defer func() { recover(); r = v }()
	v, b = 29, z/z
	_ = b
	return 0
}

// A failing type assertion as the later operand: gc holds the store back (58).
func l016FailingAssertion() (r uint64) {
	v := uint64(58)
	var iv any = "s"
	var b int
	defer func() { recover(); r = v }()
	v, b = 29, iv.(int)
	_ = b
	return 0
}

// A negative shift by a local count as the later operand: gc 29, spec 58.
func l016NegativeShift() (r uint64) {
	v := uint64(58)
	n := -1
	var b int16
	defer func() { recover(); r = v }()
	v, b = 29, 1<<n
	_ = b
	return 0
}

// A slice element as the earlier target: gc 29, spec 58.
func l016SliceElementTarget() (r uint64) {
	s := []uint64{58}
	z := int16(0)
	var b int16
	defer func() { recover(); r = s[0] }()
	s[0], b = 29, z/z
	_ = b
	return 0
}

// A dereference as the earlier target: gc 29, spec 58.
func l016DerefTarget() (r uint64) {
	v := uint64(58)
	p := &v
	z := int16(0)
	var b int16
	defer func() { recover(); r = v }()
	*p, b = 29, z/z
	_ = b
	return 0
}

// A package-level variable as the earlier target, a LOCAL divisor: gc 29.
func l016GlobalTarget() (r uint64) {
	z := int16(0)
	var b int16
	defer func() { recover(); r = gA }()
	gA, b = 29, z/z
	_ = b
	return 0
}

// A map element as the earlier target: gc 29, spec 58.
func l016MapElementTarget() (r uint64) {
	m := map[int]uint64{1: 58}
	z := int16(0)
	var b int16
	defer func() { recover(); r = m[1] }()
	m[1], b = 29, z/z
	_ = b
	return 0
}

// A field through a pointer as the earlier target: gc 29, spec 58.
func l016FieldThroughPointer() (r uint64) {
	p := &l016T{x: 58}
	z := int16(0)
	var b int16
	defer func() { recover(); r = p.x }()
	p.x, b = 29, z/z
	_ = b
	return 0
}

// A conversion of a local inside the later operand: gc 29, spec 58.
func l016ConversionOperand() (r uint64) {
	v := uint64(58)
	w := 7
	z := int16(0)
	var b int16
	defer func() { recover(); r = v }()
	v, b = 29, int16(w)/z
	_ = b
	return 0
}

// A package-level target AND a package-level divisor: gc holds back (58).
func l016GlobalTargetGlobalDivisor() (r uint64) {
	var b int16
	defer func() { recover(); r = gB }()
	gB, b = 29, zG/zG
	_ = b
	return 0
}

// A local target, a package-level divisor: gc holds back (58).
func l016LocalTargetGlobalDivisor() (r uint64) {
	v := uint64(58)
	var b int16
	defer func() { recover(); r = v }()
	v, b = 29, zG/zG
	_ = b
	return 0
}

// A package-level READ inside the later operand (the divisor local): gc holds
// back (58).
func l016GlobalReadInOperand() (r uint64) {
	v := uint64(58)
	z := int16(0)
	var b int16
	defer func() { recover(); r = v }()
	v, b = 29, (zH+z)/z
	_ = b
	return 0
}

// The two-statement control: the store is sequenced before the panic on
// both sides (29).
func l016TwoStatementsControl() (r uint64) {
	v := uint64(58)
	z := int16(0)
	var b int16
	defer func() { recover(); r = v }()
	v = 29
	b = z / z
	_ = b
	return 0
}

func main() {
	println(l016LocalDivisor())
}
