// noodler probes — classic Go gotchas with forced outcomes
// (spec#Defer_statements, spec#Goto_statements, spec#Channel_types,
// spec#Interface_types value copying, sync.Once contract).
package main

import "sync"

// goto forward over a defer statement: the defer is never registered.
func gotoOverDefer(x int) (r int) {
	if x > 0 {
		goto end
	}
	defer func() { r += 100 }()
end:
	r += 1
	return r
}

// A return inside a deferred closure returns from the closure only.
func returnInsideDeferredClosure() (r int) {
	defer func() {
		r += 1
		return
	}()
	r = 10
	return r
}

// sync.Once: a panicking f counts as done; later Do calls do nothing.
func oncePanickingCountsAsDone() int {
	var once sync.Once
	n := 0
	func() {
		defer func() { recover() }()
		once.Do(func() { n += 1; panic("in once") })
	}()
	once.Do(func() { n += 100 })
	return n
}

// Arrays travel through channels by value.
func arrayThroughChannelCopies() (int, int) {
	ch := make(chan [2]int, 1)
	a := [2]int{1, 2}
	ch <- a
	a[0] = 99
	b := <-ch
	return b[0], a[0]
}

// An array boxed into an interface is a copy.
func arrayInInterfaceCopies() int {
	a := [2]int{1, 2}
	var x any = a
	a[0] = 99
	return x.([2]int)[0]
}

// Byte arithmetic on an indexed string wraps in uint8.
func byteArithmeticWraps() (byte, byte, int) {
	s := "\xff\x01"
	return s[0] + 1, s[1] - 2, int(s[0]) + 1
}

// Rune arithmetic wraps in int32; the wrapped value converts to U+FFFD.
func runeArithmeticWraps() (rune, int) {
	r := rune(0x7fffffff)
	r++
	return r, len(string(r))
}

// A struct containing an array assigned through an interface then
// mutated: the interface copy is independent.
func structArrayInInterface() (int, int) {
	type S struct{ a [2]int }
	s := S{[2]int{1, 2}}
	var x any = s
	s.a[1] = 50
	return x.(S).a[1], s.a[1]
}

// Method value captured from a struct field path with pointers.
type Leaf struct{ n int }

func (l Leaf) Get() int { return l.n }

type Mid struct{ leaf *Leaf }
type Top struct{ mid *Mid }

func methodValueFromFieldPath() (int, int) {
	t := Top{&Mid{&Leaf{1}}}
	f := t.mid.leaf.Get
	t.mid.leaf.n = 2
	g := t.mid.leaf.Get
	t.mid.leaf = &Leaf{3}
	return f() + g(), t.mid.leaf.Get()
}

// Deferred call in a loop with break: only the executed iterations
// register defers.
func deferInLoopWithBreak() (r int) {
	for i := 1; i <= 5; i++ {
		if i == 3 {
			break
		}
		defer func() { r = r*10 + i }()
	}
	return 0
}

// Defer registered inside a recovered panic path still runs.
func deferAfterRecoverPath() (r int) {
	defer func() { r += 1 }()
	func() {
		defer func() { recover() }()
		defer func() { r += 10 }()
		panic("p")
	}()
	r += 100
	return r
}

// Closure captured before a variable's later reassignment observes the
// reassignment (variables, not values).
func closureSeesReassignment() int {
	x := 1
	f := func() int { return x }
	x = 2
	y := f()
	x = 3
	return y*10 + f()
}

// Comparing a slice/map/func to nil after make: non-nil.
func nilChecksAfterMake() (bool, bool, bool) {
	s := make([]int, 0)
	m := make(map[int]int)
	c := make(chan int)
	return s != nil, m != nil, c != nil
}

// Pointer receiver method through a map of pointers modifies the shared
// struct; a copied pointer sees it.
func sharedPointerViaMap() int {
	type C struct{ n int }
	c := &C{1}
	m := map[string]*C{"c": c}
	m["c"].n = 5
	return c.n
}

// Shadowed err-style pattern: inner := creates a new variable; the
// outer remains.
func shadowedInnerDefine() (int, int) {
	v := 1
	if true {
		v := 2
		v++
		_ = v
	}
	w := 0
	if v > 0 {
		w, v = v, 100
	}
	return v, w
}

func main() {}
