package main

func main() {
	defer func() {
		panic(recover())
	}()
	panic("orig")
}
