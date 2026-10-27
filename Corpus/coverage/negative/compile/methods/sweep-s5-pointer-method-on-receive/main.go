package main

type cnt struct{ n int }

func (c *cnt) inc() { c.n++ }

func main() {
	ch := make(chan cnt, 1)
	ch <- cnt{}
	(<-ch).inc() // a received value is not addressable
}
