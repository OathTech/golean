package main

// CSTR (Stage C audit fix round, F2; the audit's a16): `a[f()] = "s"` — a STRING
// constant copied into the phase-2 store's value cell (design §6); a is private
// (its header is read at the plan step). The subject returns 1 iff the array
// reads "xs" (the harness projects int values): {`f` · 1}; main's legacy ANF
// gives the same.
func cstr() int {
	a := []string{"x", "y"}
	f := func() int { println("f"); return 1 }
	a[f()] = "s"
	if a[0]+a[1] == "xs" {
		return 1
	}
	return 0
}

func main() { println(cstr()) }
