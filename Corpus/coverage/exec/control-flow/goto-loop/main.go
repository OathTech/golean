package main

func gotoLoop() int {
	i := 0
	sum := 0
loop:
	if i == 4 {
		return sum
	}
	sum += i
	i++
	goto loop
}

func main() {
	gotoLoop()
}
