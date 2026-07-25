package main

func switchBreakInnerLoop() int {
	total := 0
	switch 1 {
	case 1:
		for i := 0; i < 5; i++ {
			if i == 2 {
				break
			}
			total = total*10 + i
		}
		total = total + 500
	default:
		total = 9
	}
	return total
}

func main() {
	switchBreakInnerLoop()
}
