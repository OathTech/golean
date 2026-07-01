package main

func resliceCapacity() int {
	a := make([]int, 2, 5)
	b := a[:5]
	b[4] = 9
	return len(a)*1000 + cap(a)*100 + len(b)*10 + b[4]
}
