package main

func blockShadow() int {
	x := 1
	result := 0
	{
		x := 7
		result = x
	}
	return x*10 + result
}

func main() {
	blockShadow()
}
