package main

var sharedCounter = 5

func sharedBump(by int) {
	sharedCounter = sharedCounter + by
}

func sharedGlobalMutation() int {
	first := sharedCounter
	sharedBump(2)
	second := sharedCounter
	sharedBump(30)
	return first*10000 + second*100 + sharedCounter
}

func main() {
	sharedGlobalMutation()
}
