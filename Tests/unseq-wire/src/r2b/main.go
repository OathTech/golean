package main

// R2b: sinkL(left || b, change()) — E1 anchored at the COMPLETION: {"logical false 0"};
// anchored at the entry (refuted): {"logical false 0", "logical true 0"}.
func sinkL(b bool, n int) { println("logical", b, n) }

func r2b() {
	left := false
	b := false
	change := func() int { b = true; return 0 }
	sinkL(left || b, change())
}

func main() { r2b() }
