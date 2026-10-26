package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Channel targets past the receive-through-a-converted-channel of
// spec-examples-decl/conversion-parse-forms: send, len, cap and close through a
// converted channel, a defined channel type, and NAMED directional types reached
// by spec#Conversions' assignability clause (a bidirectional channel into a
// named directional type).

type MyChan chan int
type RC <-chan int
type SC chan<- int

func chanIdioms() (int, int, int, bool) {
	ch := make(chan int, 3)
	sc := (chan<- int)(ch)
	sc <- 1
	MyChan(ch) <- 2
	n := len((<-chan int)(ch))
	c := cap(MyChan(ch))
	close(sc)
	a := <-ch
	b := <-ch
	_, ok := <-(<-chan int)(ch)
	return n*10 + c, a, b, ok
}

func namedDirectionalConversion() (int, bool) {
	ch := make(chan int, 2)
	sc := SC(ch)
	rc := RC(ch)
	sc <- 3
	SC(ch) <- 4
	a := <-rc
	b := <-RC(ch)
	var i any = rc
	_, isRC := i.(RC)
	return a*10 + b, isRC && (<-chan int)(rc) == ch
}

func main() {}
