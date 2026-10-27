package main

type cnt struct{ n int }

func (c *cnt) inc() { c.n++ }

func main() {
	f := cnt.inc // inc is in *cnt's method set only
	_ = f
}
