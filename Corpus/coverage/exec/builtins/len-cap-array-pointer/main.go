package main

func builtinLenCapArrayPointer() int {
	p := &[3]int{1, 2, 3}
	return len(p)*10 + cap(p)
}

func main() {
	builtinLenCapArrayPointer()
}
