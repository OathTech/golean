package main

var multiFileTrace int

func multiFileMark(x int) int {
	multiFileTrace = multiFileTrace*10 + x
	return x
}

var multiFileB = multiFileMark(2)

func init() {
	_ = multiFileMark(4)
}

func multiFileOrder() int {
	return multiFileTrace*100 + multiFileA*10 + multiFileB
}

func main() {
	multiFileOrder()
}
