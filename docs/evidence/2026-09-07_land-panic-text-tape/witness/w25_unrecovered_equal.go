package main

func main() {
	defer func() {
		panic("a")
	}()
	panic("a")
}
