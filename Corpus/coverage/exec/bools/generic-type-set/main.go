package main

type genericBool bool

type boolLike interface {
	~bool
}

func genericNot[T boolLike](x T) bool {
	return !bool(x)
}

func genericAnd[T boolLike](a T, b T) bool {
	return bool(a && b)
}

func genericOr[T boolLike](a T, b T) bool {
	return bool(a || b)
}

func genericEqual[T boolLike](a T, b T) bool {
	return a == b
}

func genericNotEqual[T boolLike](a T, b T) bool {
	return a != b
}

func genericBoolIdentity[T boolLike](x T) T {
	return x
}

func genericBoolNotDefined() int {
	if genericNot(genericBool(false)) {
		return 1
	}
	return 0
}

func genericBoolAndOr() int {
	score := 0
	if genericAnd(genericBool(true), genericBool(true)) {
		score += 1
	}
	if !genericAnd(genericBool(true), genericBool(false)) {
		score += 10
	}
	if genericOr(genericBool(false), genericBool(true)) {
		score += 100
	}
	if !genericOr(genericBool(false), genericBool(false)) {
		score += 1000
	}
	return score
}

func genericBoolEquality() int {
	score := 0
	if genericEqual(genericBool(true), genericBool(true)) {
		score += 1
	}
	if !genericEqual(genericBool(true), genericBool(false)) {
		score += 10
	}
	if genericNotEqual(genericBool(false), genericBool(true)) {
		score += 100
	}
	if !genericNotEqual(genericBool(false), genericBool(false)) {
		score += 1000
	}
	return score
}

func genericBoolInference() int {
	x := genericBoolIdentity(genericBool(true))
	if x {
		return 1
	}
	return 0
}

func genericBoolZeroValue() int {
	var z genericBool
	if !z {
		return 1
	}
	return 0
}

func main() {
	genericBoolNotDefined()
}
