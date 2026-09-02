package main

// Campaign 3 case m3a-rerun/part-04/case_03110 (seed 5015110), reduced:
// a multi-target assignment whose THIRD right-hand operand panics
// (integer divide by zero) while the SECOND is a constant. spec#Assignment_statements:
// "First, the operands of index expressions and pointer indirections on
// the left and the expressions on the right are all evaluated in the
// usual order. Second, the assignments are carried out in left-to-right
// order." A phase-1 panic therefore precedes every phase-2 store.

// p1: constant middle RHS, panicking last RHS. spec-forced answer 58.
func probeConstStoreBeforePanic() (r uint64) {
	v := uint64(58)
	z := int16(0)
	var a, b int16
	defer func() { recover(); r = v }()
	a, v, b = -a+a, 29, z/z
	_, _ = a, b
	return 0
}

// p2: NON-constant middle RHS (a read of another local), same shape.
func probeVarStoreBeforePanic() (r uint64) {
	v := uint64(58)
	w := uint64(29)
	z := int16(0)
	var a, b int16
	defer func() { recover(); r = v }()
	a, v, b = -a+a, w, z/z
	_, _ = a, b
	return 0
}

// p3: panicking operand FIRST, constant store second.
func probePanicFirstThenConst() (r uint64) {
	v := uint64(58)
	z := int16(0)
	var b int16
	defer func() { recover(); r = v }()
	b, v = z/z, 29
	_ = b
	return 0
}

// p4: index-out-of-range instead of divide-by-zero as the panicking operand.
func probeConstStoreBeforeIndexPanic() (r uint64) {
	v := uint64(58)
	s := []int{1}
	i := 5
	var b int
	defer func() { recover(); r = v }()
	v, b = 29, s[i]
	_ = b
	return 0
}

// p5: two-target form exactly as generated: constant to v, panic to the other.
func probeTwoTargets() (r uint64) {
	v := uint64(58)
	z := int16(0)
	var b int16
	defer func() { recover(); r = v }()
	v, b = 29, z/z
	_ = b
	return 0
}

// p6: single assignment control — v = 29 then a separate panicking statement.
func probeControlSeparate() (r uint64) {
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
	println("p1", probeConstStoreBeforePanic())
	println("p2", probeVarStoreBeforePanic())
	println("p3", probePanicFirstThenConst())
	println("p4", probeConstStoreBeforeIndexPanic())
	println("p5", probeTwoTargets())
	println("p6", probeControlSeparate())
}
