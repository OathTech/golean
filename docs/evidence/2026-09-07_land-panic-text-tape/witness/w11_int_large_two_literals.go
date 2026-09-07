package main

func main() {
	defer func() {
		_ = recover()
		panic(1000)
	}()
	panic(1000)
}
