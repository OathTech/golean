package main

func repanicSameValueAbort() {
	defer func() {
		panic(recover())
	}()
	panic("orig")
}

func main() {
	repanicSameValueAbort()
}
