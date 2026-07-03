package main

func addBool[T ~bool](a T, b T) T {
	return a + b
}
