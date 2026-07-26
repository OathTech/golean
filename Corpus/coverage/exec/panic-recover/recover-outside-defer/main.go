package main

func recoverOutsideDefer() int {
	if recover() != nil {
		return 1
	}
	return 2
}

func main() {
	recoverOutsideDefer()
}
