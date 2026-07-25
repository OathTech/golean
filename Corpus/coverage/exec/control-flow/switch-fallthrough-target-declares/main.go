package main

func switchFallthroughTargetDeclares() int {
	outer := 3
	result := 0
	switch 1 {
	case 1:
		result = result*10 + 1
		fallthrough
	case 2:
		inner := outer * 2
		result = result*10 + inner
	}
	return result
}

func main() {
	switchFallthroughTargetDeclares()
}
