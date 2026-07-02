package main

func gotoForward() int {
	x := 1
	goto done
	x = 9
done:
	return x
}

func main() {
	gotoForward()
}
