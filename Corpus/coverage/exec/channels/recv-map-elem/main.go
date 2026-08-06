package main

// Audit pin (channels-arc-s1 audit S4): `m[k] = <-ch` — spec
// §Assignments phase 1 evaluates the map operand and key (lexically
// BEFORE the receive: the key's len(ch) reads the pre-receive length),
// phase 2 stores. The buffer holds {3, 4}: the first store lands at key
// len(ch) == 2 with value 3, the second drains 4 to key 0.

func recvMapElem() int {
	ch := make(chan int, 2)
	ch <- 3
	ch <- 4
	m := map[int]int{}
	m[len(ch)] = <-ch
	m[0] = <-ch
	return m[2]*100 + m[0]
}

func main() {
	recvMapElem()
}

// Delta-review pin (D5): a panicking NON-call map key (spec leaves its
// order against the receive unspecified; gc receives first) must not
// prevent the drain.
func mapKeyPanicDrains() int {
	ch := make(chan int, 1)
	ch <- 7
	m := map[int]int{}
	xs := []int{1}
	func() {
		defer func() {
			if recover() == nil {
				panic("expected a key panic")
			}
		}()
		m[xs[9]] = <-ch
	}()
	return 100 + len(ch)
}

// Convergence-round pin (BUG-030): a MAP-element FIRST target's store
// is a phase-2 event carried out in left-to-right order — it lands
// (and stays visible) even when a LATER target's store panics. The
// post-statement map-assign lowering loses it.
func mapFirstStoreLands() int {
	ch := make(chan int, 1)
	ch <- 3
	m := map[int]int{}
	var okp *bool
	hit := 0
	func() {
		defer func() {
			if recover() != nil {
				hit = 1
			}
		}()
		m[0], *okp = <-ch
	}()
	return hit*1000 + m[0]*50/3
}
