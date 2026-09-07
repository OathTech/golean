package main

func main() {
	defer func() {
		r := recover()
		panic(r.(error).Error())
	}()
	var p *int
	_ = *p
}
