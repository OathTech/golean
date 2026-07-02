package main

func structTagUnnamedConversion() int {
	x := struct {
		X int `tag:"a"`
	}{X: 8}
	y := struct {
		X int `tag:"b"`
	}(x)
	return y.X
}
