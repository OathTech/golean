package main

func main() {
	defer func() {
		_ = recover()
		panic("é")
	}()
	panic("é")
}
