package main

func value() int {
	return 1
}

func main() {
	_ = &value()
}
