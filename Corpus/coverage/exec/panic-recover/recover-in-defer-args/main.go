package main

func recoverInDeferArgs() (result int) {
	defer func(b bool) {
		if !b {
			result = 5
		}
	}(recover() != nil)
	return 1
}

func main() {
	recoverInDeferArgs()
}
