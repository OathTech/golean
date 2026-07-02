package main

func badGenericComposite[T []int | []byte]() T {
	return T{}
}
