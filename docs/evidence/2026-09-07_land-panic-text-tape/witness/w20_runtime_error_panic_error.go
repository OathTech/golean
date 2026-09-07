package main

func main() {
	defer func() {
		r := recover()
		panic(r.(error))
	}()
	var p *int
	_ = *p
}
