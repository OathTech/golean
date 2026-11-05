// Sweep lane sweep/s28-s29-spelling-symbols (2026-11-05), shape S28 (spelling admission): a
// spelling gc REJECTS; the native frontend must refuse it as a rejection too.
package main

type pt struct{ a int }

func main() {
	p := (pt){1}
	println(p.a)
}
