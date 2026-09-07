package main

func main() {
	defer func() {
		r := recover()
		panic(r)
	}()
	var p *int
	_ = *p
}
