package main

func badGenericFieldSelect[T struct{ x int }](v T) int {
	return v.x
}
