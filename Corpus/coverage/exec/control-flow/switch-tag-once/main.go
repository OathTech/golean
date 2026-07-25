package main

func bump(p *int, n int) int {
	*p = *p*10 + n
	return n
}

func switchTagOnce() int {
	trace := 0
	result := 0
	switch bump(&trace, 3) {
	case 1:
		result = 1
	case 3:
		result = 3
	}
	return trace*100 + result
}

func main() {
	switchTagOnce()
}
