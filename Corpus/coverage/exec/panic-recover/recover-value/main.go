package main

func recoverValue() (result int) {
	defer func() {
		switch r := recover().(type) {
		case int:
			result = r + 1
		default:
			result = 9
		}
	}()
	panic(4)
}

func main() {
	recoverValue()
}
