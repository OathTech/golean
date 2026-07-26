package main

func recoverStoreLocal() (result int) {
	defer func() {
		r := recover()
		if r != nil {
			result = 3
		}
	}()
	panic("store")
}

func main() {
	recoverStoreLocal()
}
