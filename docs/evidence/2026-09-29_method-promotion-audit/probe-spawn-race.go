package main

type sender interface{ Send(ch chan int) }

type spE struct{ v int }

func (e spE) Send(ch chan int) { ch <- e.v }

type spS struct {
	*spE
	z int
}

// the parent overwrites the embedded pointer after `go g.Send(ch)`: gc's
// wrapper reads p.spE in the CHILD -> a race.
func spawnPromotedPtrRace() int {
	p := &spS{spE: &spE{5}}
	var g sender = p
	ch := make(chan int)
	go g.Send(ch)
	p.spE = &spE{6}
	return <-ch
}

// the parent writes the pointee's field: races with the child's copy of *p.spE.
func spawnPromotedPteeRace() int {
	q := &spE{5}
	p := &spS{spE: q}
	var g sender = p
	ch := make(chan int)
	go g.Send(ch)
	q.v = 6
	return <-ch
}

// DRF control: disjoint field.
func spawnPromotedFree() int {
	p := &spS{spE: &spE{5}}
	var g sender = p
	ch := make(chan int)
	go g.Send(ch)
	p.z = 1
	return <-ch
}

func main() {
	println(spawnPromotedPtrRace())
}
