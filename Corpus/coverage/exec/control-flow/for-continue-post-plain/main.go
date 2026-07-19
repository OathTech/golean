package main

// continue must still run the loop post statement (i++), so i advances past 2.
// A frontend that lowers continue to skip the post makes this loop diverge.
func forContinuePostPlain() int {
	sum := 0
	last := 0
	for i := 0; i < 5; i++ {
		last = i
		if i == 2 {
			continue
		}
		sum += i
	}
	return sum*100 + last
}
