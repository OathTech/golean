package main

func closureShadowBinding() int {
	x := 1
	outer := func() int {
		return x
	}
	result := 0
	{
		x := 2
		inner := func() int {
			return x
		}
		result = outer()*100 + inner()*10 + x
	}
	return result*10 + x
}

func main() {
	closureShadowBinding()
}
