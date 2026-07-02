package main

type needsM interface {
	M()
}

func main() {
	var x needsM
	_ = x.(int)
}
