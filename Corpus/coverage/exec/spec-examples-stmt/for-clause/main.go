package main

// spec#For_clause block For_clause-2-1acd7fef: the canonical ForClause
// loop — "the init statement is executed once before evaluating the
// condition for the first iteration; the post statement is executed
// after each execution of the block". The spec shape:
// for i := 0; i < 10; i++ { f(i) }.
// Expected: f sees exactly i = 0,1,...,9 in order — 10 calls,
// sum 45, and the order-sensitive trace 0*10+0=0, then acc*10+i
// digit-chains to 123456789 (i=0 contributes a leading zero).

func forClauseTen() (int, int, int) {
	count, sum, acc := 0, 0, 0
	f := func(i int) {
		count++
		sum += i
		acc = acc*10 + i
	}
	for i := 0; i < 10; i++ {
		f(i)
	}
	return count, sum, acc
}

func main() {
	forClauseTen()
}
