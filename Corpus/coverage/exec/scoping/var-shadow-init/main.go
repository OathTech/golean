package main

func varShadowInit() int {
	x := 5
	{
		var x = x + 1
		if x != 6 {
			return -1
		}
		return x * 10
	}
}

func main() {
	varShadowInit()
}
