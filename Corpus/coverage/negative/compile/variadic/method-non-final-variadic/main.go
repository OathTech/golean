package main

type badVariadicMethod struct{}

func (badVariadicMethod) m(xs ...int, y int) {
}

func main() {
}
