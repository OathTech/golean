package main

// C1 probe (audit fix round, 2026-09-05): two goroutines, g1 = {print a; print b},
// g2 = {print c}. gc may schedule between g1's two statements (a c b);
// the machine's scheduler switches only at registry boundaries and back
// edges, so g1's registry-free segment is ATOMIC on the machine and the
// enumerator admits only {abc, cab}. Sampled with go run (plain and -race);
// see README.
func main() {
	done := make(chan int, 2)
	go func() { print("a"); print("b"); done <- 1 }()
	go func() { print("c"); done <- 1 }()
	<-done
	<-done
	print("\n")
}
