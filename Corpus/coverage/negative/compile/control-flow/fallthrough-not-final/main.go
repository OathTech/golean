package main

func main() {
	switch 1 {
	case 1:
		fallthrough
		_ = 1
	case 2:
	}
}

