package main

func main() {
	defer func() {
		_ = recover()
		panic("orig")
	}()
	panic("orig")
}
