package main

// spec#Conversions block Conversions-4-e2ad0265: a constant may be converted
// to a type-parameter type — P(1.1) is valid because 1.1 is representable by
// every float type in P's type set; the conversion yields a NON-constant
// value of the instantiated type, computed per instantiation (float32
// rounding is visible for the ~float32 member).

type myF32 float32

func f[P ~float32 | ~float64]() P {
	return P(1.1) // the block's elided body around P(1.1)
}

func genericConversionF64() float64 {
	return float64(f[float64]())
}

func genericConversionF32() float64 {
	return float64(f[myF32]()) // float32(1.1): rounded
}
