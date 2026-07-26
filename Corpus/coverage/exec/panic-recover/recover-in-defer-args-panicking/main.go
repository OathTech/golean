package main

func recoverInDeferArgsPanicking() (result int) {
	defer func() {
		if recover() != nil {
			result = result*10 + 1
		}
	}()
	defer func() {
		defer func(b bool) {
			if b {
				result = result*10 + 2
			}
		}(recover() != nil)
		result = result*10 + 3
	}()
	panic("boom")
}

func main() {
	recoverInDeferArgsPanicking()
}
