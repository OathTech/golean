package main

// A LABELED switch inside a for loop, with a bare `continue` in one
// clause and `break sw` in another: the bare continue signal must pass
// THROUGH the switch's label continuation (machine arm labelContinue)
// to reach the enclosing loop, while `break sw` matches the labelK and
// terminates only the switch. Differential coverage for the bare-signal
// labelK passthrough (audit-response 2026-08-04, F3).
func labeledSwitchBareContinue() int {
	n := 0
	for i := 0; i < 4; i++ {
	sw:
		switch i {
		case 0:
			n = n*10 + 1
			continue
		case 1:
			break sw
		case 2:
			n = n*10 + 2
		}
		n = n*10 + 3
	}
	return n
}

func main() {
	labeledSwitchBareContinue()
}
