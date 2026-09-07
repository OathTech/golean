package main

func main() {
	defer func() {
		_ = recover()
		s := "orig"
		panic(s)
	}()
	panic("orig")
}
