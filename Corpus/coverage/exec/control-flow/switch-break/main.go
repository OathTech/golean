package main

func switchBreak() int {
	result := 0
	trace := 0
	switch 2 {
	case 1:
		result = 1
	case 2:
		trace = 5
		if trace == 5 {
			break
		}
		trace = 99
	case 3:
		result = 3
	}
	return trace*10 + result
}

func main() {
	switchBreak()
}
