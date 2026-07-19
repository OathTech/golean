package main

type ctr int

func (c ctr) inc() ctr { return c + 1 }

func methodSmoke() int {
	var c ctr = 41
	c = c.inc()
	return int(c)
}
