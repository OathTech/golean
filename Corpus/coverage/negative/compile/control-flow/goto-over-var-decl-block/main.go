package main

func main() {
	{
		goto L
		x := 1
	L:
		_ = x
	}
}
