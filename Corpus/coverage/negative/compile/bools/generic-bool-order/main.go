package main

func orderBool[T ~bool](a T, b T) bool {
	return a < b
}
