package main

func continueInSwitch() int {
	result := 0
	for i := 0; i < 4; i++ {
		switch i {
		case 1, 3:
			continue
		}
		result = result*10 + i + 1
	}
	return result
}
