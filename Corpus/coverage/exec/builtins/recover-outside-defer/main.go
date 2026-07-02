package main

func builtinRecoverOutsideDefer() int {
	if recover() == nil {
		return 1
	}
	return 0
}

func main() {
	builtinRecoverOutsideDefer()
}
