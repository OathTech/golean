package main

var multiValueTrace int

func multiValueTwo() (int, int) {
	multiValueTrace = multiValueTrace*10 + 1
	return 4, 7
}

var multiValueSum = multiValueA + multiValueB
var multiValueA, multiValueB = multiValueTwo()

func multiValueVarInit() int {
	return (multiValueTrace*10+multiValueA)*100 + multiValueB*10 + multiValueSum
}

func main() {
	multiValueVarInit()
}
