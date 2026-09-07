package main

func main() {
	defer func() {
		r := recover()
		panic(r.(bool))
	}()
	panic(true)
}
