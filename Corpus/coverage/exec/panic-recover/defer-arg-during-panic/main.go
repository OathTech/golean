package main

func deferArgDuringPanic() (result int) {
	x := 1
	defer func(captured int) {
		if recover() != nil {
			result = captured
		}
	}(x)
	x = 9
	panic("boom")
}

func main() {
	deferArgDuringPanic()
}
