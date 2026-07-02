package main

func recoverInNestedFrame() (result int) {
	defer func() {
		if recover() != nil {
			result = 4
		}
	}()
	panic("nested panic")
}

func nestedFrameRecover() int {
	return recoverInNestedFrame()*10 + 1
}

func main() {
	nestedFrameRecover()
}
