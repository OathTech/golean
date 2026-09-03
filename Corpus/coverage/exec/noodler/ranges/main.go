// noodler probes — range semantics (spec#For_range): the range
// expression is evaluated once; arrays are copied, array pointers and
// slices are not; the assignment form with identifier targets.
package main

// Assignment-form range with pre-declared identifier targets; final
// values survive the loop.
func assignFormIdentifiers() (int, int) {
	var i, v int
	s := []int{5, 6, 7}
	for i, v = range s {
	}
	return i, v
}

// Assignment form over a string and a map with a single key.
func assignFormStringAndMap() (int, rune, string) {
	var i int
	var r rune
	for i, r = range "aé" {
	}
	var k string
	for k = range map[string]int{"only": 1} {
	}
	return i, r, k
}

// Ranging over an array VALUE iterates the copy: writes to the array
// during iteration are not seen.
func arrayValueCopyDuringRange() int {
	arr := [3]int{1, 2, 3}
	sum := 0
	for i, v := range arr {
		if i == 0 {
			arr[1] = 100
			arr[2] = 100
		}
		sum += v
	}
	return sum
}

// Ranging over an array POINTER sees writes made during iteration.
func arrayPointerSeesWrites() int {
	arr := [3]int{1, 2, 3}
	p := &arr
	sum := 0
	for i, v := range p {
		if i == 0 {
			p[1] = 100
			p[2] = 100
		}
		sum += v
	}
	return sum
}

// Ranging over a slice sees writes to elements not yet reached.
func sliceSeesWrites() int {
	s := []int{1, 2, 3}
	sum := 0
	for i, v := range s {
		if i == 0 {
			s[2] = 100
		}
		sum += v
	}
	return sum
}

// Range over an array of structs by value copies each element.
func arrayOfStructsCopies() (int, int) {
	type P struct{ x int }
	ps := []P{{1}, {2}}
	for _, p := range ps {
		p.x = 100
	}
	a := ps[0].x + ps[1].x
	for i := range ps {
		ps[i].x = 100
	}
	return a, ps[0].x + ps[1].x
}

// Range over an integer expression evaluated once, even if its inputs
// change in the body.
func rangeIntEvaluatedOnce() int {
	n := 3
	count := 0
	for range n * 2 {
		n = 100
		count++
	}
	return count
}

// Range over an empty array and a length-3 array index-only.
func rangeEmptyAndIndexOnly() (int, int) {
	var e [0]int
	a := 0
	for range e {
		a++
	}
	b := 0
	for i := range [3]string{} {
		b += i + 1
	}
	return a, b
}

// Range over a slice reassigned in the body: the original is iterated.
func sliceReassignedInBody() int {
	s := []int{1, 2, 3}
	sum := 0
	for _, v := range s {
		s = []int{100, 100}
		sum += v
	}
	return sum + len(s)
}

// Range over a nil array pointer with index-only is fine; with a value
// it panics.
func nilArrayPointerIndexOnly() int {
	var p *[4]int
	n := 0
	for i := range p {
		n += i
	}
	return n
}

func nilArrayPointerValue() int {
	var p *[4]int
	n := 0
	for _, v := range p {
		n += v
	}
	return n
}

// Labeled continue inside range over a channel.
func labeledContinueRangeChan() int {
	ch := make(chan int, 4)
	for i := 1; i <= 4; i++ {
		ch <- i
	}
	close(ch)
	sum := 0
outer:
	for v := range ch {
		for j := 0; j < 3; j++ {
			if v%2 == 0 {
				continue outer
			}
			sum += v
		}
	}
	return sum
}

// Range over a string builds rune and byte sums separately.
func stringRuneAndByteSums() (int, int) {
	s := "aé€"
	rs, bs := 0, 0
	for _, r := range s {
		rs += int(r)
	}
	for i := 0; i < len(s); i++ {
		bs += int(s[i])
	}
	return rs, bs
}

// Range variable of a typed integer range takes the operand's type.
func rangeTypedIntVar() (int16, bool) {
	var n int16 = 3
	var last int16
	for i := range n {
		last = i
	}
	var check any = last
	_, ok := check.(int16)
	return last, ok
}

func main() {}
