package main

type methodValueCallbackCounter struct {
	n int
}

func (c *methodValueCallbackCounter) add(x int) int {
	c.n += x
	return c.n
}

func callCallback(f func(int) int) int {
	return f(3)*10 + f(4)
}

func methodValueCallback() int {
	c := methodValueCallbackCounter{n: 1}
	return callCallback(c.add)
}

func main() {
	methodValueCallback()
}
