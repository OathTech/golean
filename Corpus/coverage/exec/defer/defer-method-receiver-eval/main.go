package main

type deferMethodCounter struct {
	n int
}

func (c deferMethodCounter) Save(dst *int) {
	*dst = c.n
}

func deferMethodReceiverEval() (result int) {
	c := deferMethodCounter{n: 1}
	defer c.Save(&result)
	c.n = 9
	return 0
}

func main() {
	deferMethodReceiverEval()
}
