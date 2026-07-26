package main

func recoverLoopDefer() (result int) {
	for i := 1; i <= 3; i++ {
		defer func(n int) {
			if recover() != nil {
				result = result*100 + n*10 + 1
			} else {
				result = result*100 + n*10
			}
		}(i)
	}
	panic("loop")
}

func main() {
	recoverLoopDefer()
}
