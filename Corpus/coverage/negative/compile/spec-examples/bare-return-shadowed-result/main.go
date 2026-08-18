// spec#Return_statements block Return_statements-6-a013b9d5: empty-expression return invalid where result parameter err is shadowed
// LATITUDE NOTE (P3 audit S2 / ledger L-010): the governing prose is a
// MAY implementation restriction — this case pins gc's realization
// (rejection), not a spec-forced rejection; a conforming implementation
// could accept this program. The spec's own exhibit labels the line
// "invalid", which is the L-010 prose-vs-exhibit tension.
package main

func f(n int) (res int, err error) {
	if _, err := f(n - 1); err != nil {
		return // invalid return statement: err is shadowed
	}
	return
}

func main() { _, _ = f(0) }
