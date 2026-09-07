package main

func equalHandler() {
	_ = recover()
	panic("orig")
}

func thirdHandler() {
	_ = recover()
	panic("third")
}

func main() {
	defer thirdHandler()
	defer equalHandler()
	panic("orig")
}
