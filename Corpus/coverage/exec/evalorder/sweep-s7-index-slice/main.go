package main

// Defect-neighbourhood campaign, shape S7 (ordered events reordered by the hoist),
// lane sweep/s7-hoist-order, 2026-10-27: plan docs/2026-10-27_defect-neighbourhood-campaign.md
// §4 ([USER]-approved 2026-10-27); the matrix is on the member entries' Neighbourhood lines
// in docs/BUGS.md (BUG-113/062/058/026/023/145/144). spec#Order_of_evaluation: function
// calls, method calls, receive operations and binary logical operations are evaluated in
// lexical left-to-right order. Each subject returns its event log (a closure appends the
// name of each event as it runs); where a receive is in play its VALUE attests its order
// against a call that non-blockingly swaps the buffered element ("r1" if the receive came
// first, "after" if the call did).
//
// INDEX AND SLICE EXPRESSIONS: a called base and a called index, an index that is a receive
// before a call, a called map and key, slice expressions with two and three called bounds, a
// called string and index, an indexed call before a call. All born green.

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	s := ""
	for n > 0 {
		s = string(rune('0'+n%10)) + s
		n /= 10
	}
	return s
}

func e1() string {
	log := ""
	s := func() []string { log += "s "; return []string{"X", "Y"} }
	i := func() int { log += "i "; return 1 }
	v := s()[i()]
	return log + v
}

func e2() string {
	log := ""
	ch := make(chan int, 2)
	ch <- 0
	xs := []string{"X", "Y"}
	f := func() string {
		log += "f "
		select {
		case <-ch:
			ch <- 1
		default:
		}
		return "F"
	}
	sink := func(x, y string) { log += "sink(" + x + "," + y + ") " }
	sink(xs[<-ch], f())
	return log
}

func e3() string {
	log := ""
	mm := map[string]string{"k": "V"}
	m := func() map[string]string { log += "m "; return mm }
	k := func() string { log += "k "; return "k" }
	v := m()[k()]
	return log + v
}

func e4() string {
	log := ""
	s := func() []int { log += "s "; return []int{1, 2, 3, 4} }
	a := func() int { log += "a "; return 1 }
	b := func() int { log += "b "; return 3 }
	r := s()[a():b()]
	return log + itoa(len(r))
}

func e4t() string {
	log := ""
	s := []int{1, 2, 3, 4}
	a := func() int { log += "a "; return 1 }
	b := func() int { log += "b "; return 3 }
	c := func() int { log += "c "; return 4 }
	r := s[a():b():c()]
	return log + itoa(len(r)) + itoa(cap(r))
}

func e5() string {
	log := ""
	str := func() string { log += "str "; return "xyz" }
	i := func() int { log += "i "; return 1 }
	v := string(str()[i()])
	return log + v
}

func e6() string {
	log := ""
	xs := []int{10, 20}
	i := func() int { log += "i "; return 1 }
	f := func() int { log += "f "; return 5 }
	v := xs[i()] + f()
	return log + itoa(v)
}

func main() {
	e1()
	e2()
	e3()
	e4()
	e4t()
	e5()
	e6()
}
