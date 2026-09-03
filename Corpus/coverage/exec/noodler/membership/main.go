// noodler probes — membership-lane rows whose admitted sets the spec
// bounds exactly; the check is two-sided (gc samples inside the set;
// the set no larger than the spec allows).
package main

// Two goroutines each send their id into a cap-2 buffer; main drains.
// Admitted: {12, 21}. mem#chan gives no order between the two sends.
func twoSendersBuffered() int {
	ch := make(chan int, 2)
	go func() { ch <- 1 }()
	go func() { ch <- 2 }()
	a := <-ch
	b := <-ch
	return a*10 + b
}

// Three-key map ranged once: the 6 permutations (spec#For_statements:
// "the iteration order over maps is not specified").
func threeKeyMapOrder() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	r := 0
	for k := range m {
		r = r*10 + k
	}
	return r
}

// Two ready buffered channels in a select: {1, 2}.
func selectTwoReady() int {
	a := make(chan int, 1)
	b := make(chan int, 1)
	a <- 1
	b <- 2
	select {
	case v := <-a:
		return v
	case v := <-b:
		return v
	}
}

// Deleting an UNREACHED key during range must suppress it; deleting the
// current key is fine. Over a 2-key map: the observable is the number
// of iterations — always 1 (spec: "the corresponding iteration value
// will not be produced"). Strict lane: the machine must not admit 2.
func deleteOtherKeyDuringRange() int {
	m := map[int]int{1: 1, 2: 2}
	n := 0
	for k := range m {
		n++
		delete(m, 3-k)
	}
	return n
}

// Ranging a map while inserting a key that is later deleted before it
// could be produced: the new key may be produced or skipped, but the
// count is bounded by 3 (2 originals + at most 1 production of key 9).
func insertThenDeleteDuringRange() int {
	m := map[int]int{1: 1, 2: 2}
	n := 0
	for k := range m {
		n++
		if k == 1 {
			m[9] = 9
		}
		if k == 2 {
			delete(m, 9)
		}
	}
	return n
}

func main() {}
