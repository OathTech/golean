package main

func switchBreakContinueInterleave() int {
	total := 0
	for i := 0; i < 3; i++ {
		switch i {
		case 0:
			for j := 0; j < 9; j++ {
				if j == 2 {
					break
				}
				total = total*10 + j
			}
		case 1:
			continue
		default:
			break
		}
		total = total*10 + 7
	}
	return total
}

func main() {
	switchBreakContinueInterleave()
}
