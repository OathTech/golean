package main

type genericFloat32 float32
type genericFloat64 float64

type genericFloat interface {
	~float32 | ~float64
}

func genericFloatSum[T genericFloat](a T, b T) T {
	return a + b
}

func genericFloatCompound[T genericFloat](a T, b T) T {
	a += b
	a *= 2
	a /= 4
	return a
}

func genericFloatOrder[T genericFloat](a T, b T) int {
	if a < b {
		return 1
	}
	if a == b {
		return 2
	}
	return 3
}

func genericFloatToInt[T genericFloat](x T) int {
	return int(x)
}

func genericFloatExplicitLiteral[T genericFloat]() T {
	return T(1.25)
}

func genericFloatInferred[T genericFloat](x T) T {
	return x + T(0.5)
}

func genericFloat32DefinedSum() int {
	if genericFloatSum(genericFloat32(1.5), genericFloat32(2.25)) == genericFloat32(3.75) {
		return 1
	}
	return 0
}

func genericFloat64DefinedSum() int {
	if genericFloatSum(genericFloat64(2.5), genericFloat64(4.5)) == genericFloat64(7) {
		return 1
	}
	return 0
}

func genericFloatCompoundAssign() int {
	if genericFloatCompound(genericFloat64(6), genericFloat64(2)) == genericFloat64(4) {
		return 1
	}
	return 0
}

func genericFloatOrdering() int {
	return genericFloatOrder(float32(1), float32(2))*100 +
		genericFloatOrder(float64(2), float64(2))*10 +
		genericFloatOrder(genericFloat64(3), genericFloat64(2))
}

func genericFloatConversionToInt() int {
	return genericFloatToInt(float32(2.9))*10 + genericFloatToInt(genericFloat64(-2.9))
}

func genericFloatExplicitConstant() int {
	if genericFloatExplicitLiteral[genericFloat32]() == genericFloat32(1.25) {
		return 1
	}
	return 0
}

func genericFloatInference() int {
	if genericFloatInferred(float64(2)) == float64(2.5) {
		return 1
	}
	return 0
}

func genericFloatZeroValue() int {
	var z genericFloat64
	if z == 0 {
		return 1
	}
	return 0
}

func main() {
	genericFloat32DefinedSum()
}
