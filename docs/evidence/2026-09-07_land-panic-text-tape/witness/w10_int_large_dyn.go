package main

func main() {
	defer func() {
		r := recover()
		panic(r.(int))
	}()
	panic(1000)
}
