package main

type variadicReceiver struct{}

func (variadicReceiver) m(xs ...int) {
}

func main() {
	xs := []string{"bad"}
	variadicReceiver{}.m(xs...)
}
