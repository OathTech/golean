package main

func deferUnnamedReturn() int {
	x := 1
	defer func() {
		x = 9
	}()
	return x
}

func main() {
	deferUnnamedReturn()
}
