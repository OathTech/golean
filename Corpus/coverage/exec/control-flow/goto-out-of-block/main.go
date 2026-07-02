package main

func gotoOutOfBlock() int {
	x := 1
	{
		x = 2
		goto done
		x = 9
	}
done:
	return x
}

func main() {
	gotoOutOfBlock()
}
