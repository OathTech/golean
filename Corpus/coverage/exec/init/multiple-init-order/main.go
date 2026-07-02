package main

var multipleInitTrace int

func init() {
	multipleInitTrace = multipleInitTrace*10 + 1
}

func init() {
	multipleInitTrace = multipleInitTrace*10 + 2
}

func multipleInitOrder() int {
	return multipleInitTrace
}

func main() {
	multipleInitOrder()
}
