package main

type genericComplex64 complex64
type genericComplex128 complex128
type genericComplexA complex128
type genericComplexB complex128

type genericComplex interface {
	~complex64 | ~complex128
}

func genericComplexSum[T genericComplex](a T, b T) T {
	return a + b
}

func genericComplexCompound[T genericComplex](a T, b T) T {
	a += b
	a *= T(1i)
	return a
}

func genericComplexEqual[T genericComplex](a T, b T) int {
	if a == b {
		return 1
	}
	return 0
}

func genericComplexDivide[T genericComplex](a T, b T) T {
	return a / b
}

func genericComplexExplicit[T genericComplex]() T {
	return T(1 + 2i)
}

func genericComplexConvert[A ~complex128, B ~complex128](x A) B {
	return B(x)
}

func genericComplex64DefinedSum() int {
	z := genericComplexSum(genericComplex64(1+2i), genericComplex64(3-1i))
	if z == genericComplex64(4+1i) {
		return 1
	}
	return 0
}

func genericComplex128DefinedSum() int {
	z := genericComplexSum(genericComplex128(2+3i), genericComplex128(-1+4i))
	if z == genericComplex128(1+7i) {
		return 1
	}
	return 0
}

func genericComplexCompoundAssign() int {
	z := genericComplexCompound(genericComplex128(1+2i), genericComplex128(3+4i))
	if z == genericComplex128(-6+4i) {
		return 1
	}
	return 0
}

func genericComplexDivision() int {
	z := genericComplexDivide(complex128(1+1i), complex128(1-1i))
	if z == complex128(1i) {
		return 1
	}
	return 0
}

func genericComplexEquality() int {
	return genericComplexEqual(complex64(1+2i), complex64(1+2i))*10 +
		genericComplexEqual(genericComplex128(1), genericComplex128(2))
}

func genericComplexExplicitConstant() int {
	if genericComplexExplicit[genericComplex64]() == genericComplex64(1+2i) {
		return 1
	}
	return 0
}

func genericComplexConversion() int {
	if genericComplexConvert[genericComplexA, genericComplexB](genericComplexA(3+4i)) == genericComplexB(3+4i) {
		return 1
	}
	return 0
}

func genericComplexInference() int {
	if genericComplexInferenceValue(genericComplex64(2+3i)) == genericComplex64(2+4i) {
		return 1
	}
	return 0
}

func genericComplexInferenceValue[T genericComplex](x T) T {
	return x + T(1i)
}

func genericComplexZeroValue() int {
	var z genericComplex128
	if z == 0 {
		return 1
	}
	return 0
}

func main() {
	genericComplex64DefinedSum()
}
