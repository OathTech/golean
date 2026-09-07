package main

func main() {
	defer func() {
		r := recover()
		panic(r.(string))
	}()
	panic("orig")
}
