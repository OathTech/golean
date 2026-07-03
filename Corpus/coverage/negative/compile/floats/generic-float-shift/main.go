package main

type genericFloatShiftConstraint interface {
	~float32 | ~float64
}

func genericFloatShiftBad[T genericFloatShiftConstraint](a T) T {
	return a << 1
}

func main() {
	_ = genericFloatShiftBad(float64(1))
}
