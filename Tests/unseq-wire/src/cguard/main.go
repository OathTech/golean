package main

// CGUARD (Stage C audit fix round, F2; the audit's a14): `ok := true && f()` — a
// CONSTANT guard test copied into a bool cell (design §6). f sets the captured a.
// Singleton {2}; main's legacy ANF gives 2.
func cguard() int {
	a := 1
	f := func() bool { a = 2; return true }
	ok := true && f()
	if ok {
		return a
	}
	return -1
}

func main() { println(cguard()) }
