package main

// A pure, registry-free delay (a finite recursion: no loop back-edge, no
// registry op) between the parent's two prints. It makes gc exhibit the
// child's print between them at a useful rate; the machine's set does
// not depend on it.
//
//go:noinline
func gapDelay(n int) int {
	if n == 0 {
		return 0
	}
	return n + gapDelay(n-1)
}

// The parent prints A, delays, prints C; a child prints B and signals.
// Ledger FR-30 (recorded 2026-09-05; the Codex release-trust review's R2
// witness, 2026-10-12, relayed by the [USER]; BUG-123): gc's `printlock`
// makes ONE statement atomic and lets any goroutine write between
// statements, so the child's B may land before A (BAC), between A and C
// (ABC) or after C (ACB). On `main` before this lane a goroutine's
// consecutive prints in a registry-free segment were atomic on the
// machine (no scheduling point between them): DFS certified exactly
// {ACB, BAC}; gc go1.26.5 (GOMAXPROCS=2, 1,000 calls) realized
// ACB/ABC/BAC at 891/107/2 under -race and 993/7/0 plain. The print
// apply is a registry boundary since this lane: certified set
// {ABC, ACB, BAC} (members=3). Membership lane: observed ∈ the set.
func goroutineGap() int {
	done := make(chan int)
	go func() {
		print("B")
		done <- 1
	}()
	print("A")
	_ = gapDelay(100)
	print("C")
	<-done
	return 0
}

func main() {
	goroutineGap()
	println()
}
