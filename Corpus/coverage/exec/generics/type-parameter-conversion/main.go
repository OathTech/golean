package main

type genericA int
type genericB int

func convertGenericInt[T ~int, U ~int](x T) U {
	return U(x + 1)
}

func genericTypeParameterConversion() int {
	x := convertGenericInt[genericA, genericB](genericA(6))
	return int(x)
}
