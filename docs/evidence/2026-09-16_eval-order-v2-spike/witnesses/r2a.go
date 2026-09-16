package main

// R2 witness (skip): the || region's event h is skipped when z is true; k still
// runs — E1 anchors k after the || COMPLETION, which the skip discharges. Two
// sweeps: z true, then z false. Each relation set is a singleton; no stuck outcome.
func main() {
	h := func() bool { println("guard h"); return true }
	k := func() int { println("guard k"); return 7 }
	sink := func(b bool, n int) { println("guard result", b, n) }
	z := true
	sink(z || h(), k())
	z = false
	sink(z || h(), k())
}
