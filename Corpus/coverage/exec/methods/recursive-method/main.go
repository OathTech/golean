package main

type countdown struct {
	n int
}

func (c countdown) sum() int {
	if c.n == 0 {
		return 0
	}
	return c.n + (countdown{n: c.n - 1}).sum()
}

func recursiveMethod() int {
	return (countdown{n: 4}).sum()
}
