package main

type unaryInt func(int) int

func hoiIdentity[T any](x T) T {
	return x
}

func hoiAddOne[T ~int](x T) T {
	return x + 1
}

func hoiFirst[A any, B any](a A, b B) A {
	_ = b
	return a
}

func hoiApply[T any](f func(T) T, x T) T {
	return f(x)
}

func hoiTwice(f func(int) int, x int) int {
	return f(f(x))
}

func hoiUseFirst(f func(int, string) int) int {
	return f(4, "xx")
}

func hoiReturnIntIdentity() func(int) int {
	return hoiIdentity
}

func higherOrderInferencePassToGeneric() int {
	return hoiApply(hoiIdentity, 7)
}

func higherOrderInferencePassToConcrete() int {
	return hoiTwice(hoiAddOne, 5)
}

func higherOrderInferenceAssignmentTarget() int {
	var f func(string) string = hoiIdentity
	return len(f("abc"))
}

func higherOrderInferenceNamedFunctionType() int {
	var f unaryInt = hoiAddOne
	return f(8)
}

func higherOrderInferenceReturnTarget() int {
	return hoiReturnIntIdentity()(9)
}

func higherOrderInferencePartialInstantiationTarget() int {
	return hoiUseFirst(hoiFirst[int])
}
