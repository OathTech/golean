// spec#For_clause block For_clause-5-ceac0281
// The spec's per-iteration loop-variable example [Go 1.22]: closures
// created across iterations of `for i := 0; i < 5; i++ { ...; i++ }`
// capture DISTINCT variables and observe 1, 3, 5 (the body's i++
// happens after capture-site creation but on the same iteration's
// variable). The spec's println outputs become digits of the returned
// int: 135. Block For_clause-6-930576d8 (the pre-Go-1.22 output
// 6 6 6) is the superseded semantics and is deliberately NOT pinned
// here — version skew is divergence-ledger material.
package main

func loopvarPerIteration() int {
	var fns []func() int
	for i := 0; i < 5; i++ {
		fns = append(fns, func() int { return i })
		i++
	}
	acc := 0
	for _, f := range fns {
		acc = acc*10 + f()
	}
	return acc // 135
}

func main() {
	loopvarPerIteration()
}
