package main

func fullSliceBounds() {
	a := []int{1, 2, 3}
	m := 4
	s := a[0:2:m]
	_ = len(s)
}

func main() {
	fullSliceBounds()
}
