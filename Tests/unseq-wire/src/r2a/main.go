package main

// R2a: sinkB(z || h(), k()) — a skipped region discharges the E1 edge to k.
// z=true: {"guard k / guard result true 7"}; z=false: {"guard h / guard k / guard result true 7"}.
func h() bool  { println("guard h"); return true }
func k() int   { println("guard k"); return 7 }
func sinkB(b bool, n int) { println("guard result", b, n) }

func r2aTrue() {
	z := true
	sinkB(z || h(), k())
}

func r2aFalse() {
	z := false
	sinkB(z || h(), k())
}

func main() { r2aTrue(); r2aFalse() }
