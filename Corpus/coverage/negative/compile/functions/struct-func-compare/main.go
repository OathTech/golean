package main

type holder struct {
	f func()
}

func main() {
	var a, b holder
	_ = a == b
}
