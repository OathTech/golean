package main

func recoverRepanic() {
	defer func() {
		if recover() != nil {
			panic("wrapped panic")
		}
	}()
	panic("inner panic")
}

func main() {
	recoverRepanic()
}
