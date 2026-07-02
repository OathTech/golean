package main

type deferPointerCell struct {
	n int
}

func (c *deferPointerCell) save(dst *int) {
	*dst = c.n
}

func deferPointerReceiverLive() (result int) {
	c := &deferPointerCell{n: 1}
	defer c.save(&result)
	c.n = 9
	return 0
}
