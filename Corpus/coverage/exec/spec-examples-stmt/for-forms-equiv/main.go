package main

// spec#For_clause block For_clause-3-d61c1c53: "Any element of the
// ForClause may be empty ... If the condition is absent, it is
// equivalent to the boolean value true":
//   for cond { S() }  is the same as  for ; cond ; { S() }
//   for      { S() }  is the same as  for true     { S() }
// Expected: with the same S (count-and-stop-at-4 via break for the
// condition-free forms; a decreasing cond for the first pair), each
// pair runs S the identical number of times: (4, 4) and (4, 4).

func forFormsCondPair() (int, int) {
	n1 := 0
	cond1 := func() bool { return n1 < 4 }
	for cond1() {
		n1++
	}
	n2 := 0
	cond2 := func() bool { return n2 < 4 }
	for ; cond2(); {
		n2++
	}
	return n1, n2
}

func forFormsInfinitePair() (int, int) {
	n1 := 0
	for {
		n1++
		if n1 == 4 {
			break
		}
	}
	n2 := 0
	for true {
		n2++
		if n2 == 4 {
			break
		}
	}
	return n1, n2
}

func main() {
	forFormsCondPair()
}
