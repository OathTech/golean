package main

// DESIGNED RED (audit fix round A2, 2026-09-05; BUG-093; FR-29 iv): a racy
// program that PRINTS. TSan's report interleaves asynchronously with the
// program's fd-2 bytes, so the split refuses any byte before the report
// ("race rows with program output are not comparable"); bytes printed AFTER
// the report are not detected (the recorded limitation). The row is red at
// stage go-observation by the split's own name.
func raceWithOutput() int {
	println("racing")
	x := 0
	done := make(chan int)
	go func() {
		x = 1
		done <- 1
	}()
	x = 2
	<-done
	return x
}
