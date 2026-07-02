package main

func badGenericCompare[T any](x T, y T) bool {
	return x == y
}
