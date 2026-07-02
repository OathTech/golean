package main

func constantDivision() int {
	const intDiv = 5 / 2
	const floatDiv = 5.0 / 2
	return intDiv*100 + int(floatDiv*10)
}

func main() {
	constantDivision()
}
