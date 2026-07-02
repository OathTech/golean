package main

func gotoBackwardRedeclare() int {
	count := 0
	sum := 0
loop:
	x := count + 1
	sum += x
	count++
	if count < 3 {
		goto loop
	}
	return sum
}
