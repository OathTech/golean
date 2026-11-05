// Sweep lane sweep/s28-s29-spelling-symbols (2026-11-05), shape S28 (spelling admission): a
// spelling gc REJECTS; the native frontend must refuse it as a rejection too.
package main

func main() {
	m := map[string]int{"a": 1, "a": 2}
	println(len(m))
}
