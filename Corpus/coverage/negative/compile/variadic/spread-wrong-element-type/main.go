package main

func takesInts(xs ...int) {
}

func main() {
	xs := []string{"bad"}
	takesInts(xs...)
}
