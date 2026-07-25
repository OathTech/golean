package main

func closureBlockScopeCapture() int {
	x := 1
	var f func()
	{
		y := 2
		f = func() { x = x*10 + y }
	}
	f()
	f()
	return x
}

func main() {
	closureBlockScopeCapture()
}
