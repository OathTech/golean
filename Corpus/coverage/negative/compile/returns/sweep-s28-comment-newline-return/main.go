// Sweep lane sweep/s28-s29-spelling-symbols (2026-11-05), shape S28 (spelling admission): a
// spelling gc REJECTS; the native frontend must refuse it as a rejection too.
package main

func f() int {
	x := 1
	return /*
	*/ x
}

func main() { println(f()) }
