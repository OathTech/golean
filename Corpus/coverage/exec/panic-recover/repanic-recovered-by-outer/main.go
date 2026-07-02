package main

func repanicRecoveredByOuter() (result int) {
	defer func() {
		if recover() != nil {
			result = result*10 + 1
		}
	}()
	defer func() {
		if recover() != nil {
			result = result*10 + 2
			panic("second panic")
		}
	}()
	panic("first panic")
}

func main() {
	repanicRecoveredByOuter()
}
