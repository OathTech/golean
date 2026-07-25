package main

func switchBreakInLoop() int {
	total := 0
	for i := 0; i < 4; i++ {
		switch i {
		case 1:
			total = total*10 + 1
			break
		case 2:
			continue
		default:
			total = total*10 + 9
		}
		total = total + 100
	}
	return total
}

func main() {
	switchBreakInLoop()
}
