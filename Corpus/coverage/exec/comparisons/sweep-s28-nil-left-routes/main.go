// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). BUG-136's neighbours: `nil` on
// the LEFT at the routes beyond the entry's rows (a call, a field, an element, a receive,
// an if / for / define / switch position, an assertion, a boxed pointer), and the
// PARENTHESISED nil on either side at every sink; expected = gc go1.26.5.

package main

type node struct {
	next *node
	fn   func() int
}

func getp() *node { return nil }

func nilLeftRoutes() int {
	var p *node
	n := node{}
	s := []*node{nil}
	m := map[string]*node{}
	ch := make(chan *node, 1)
	ch <- nil
	r := 0
	if nil != p {
		r += 1
	}
	if nil == getp() {
		r += 10
	}
	if nil == n.next {
		r += 100
	}
	if nil == s[0] {
		r += 1000
	}
	if nil == m["x"] {
		r += 10000
	}
	if nil == <-ch {
		r += 100000
	}
	q := &n
	for nil != q {
		q = q.next
		r += 1000000
	}
	x := nil == p
	if x {
		r += 10000000
	}
	switch {
	case nil == p:
		r += 100000000
	}
	switch p {
	case nil:
		r += 1000000000
	}
	return r // 1111111110
}

func nilLeftBoxedAndAssert() int {
	var p *node
	var i any = p
	r := 0
	if nil == i {
		r += 1 // a typed nil box is not nil
	}
	if nil == i.(*node) {
		r += 10
	}
	if nil == any(p) {
		r += 100
	}
	var e error
	if nil == e {
		r += 1000
	}
	if (nil) == e {
		r += 10000
	}
	if nil == n.fn {
		r += 100000
	}
	return r // 111010
}

var n node

func take(p *node) int {
	if p == nil {
		return 1
	}
	return 0
}

func retNil() *node { return (nil) }

func parenNilSinks() int {
	var p *node
	var q *node = (nil)
	r := 0
	if (p) == nil {
		r += 1
	}
	if nil == (p) {
		r += 10
	}
	if (nil) == p {
		r += 100
	}
	if p == (nil) {
		r += 1000
	}
	if (nil) != (p) {
		r += 10000
	}
	r += take((nil)) * 100000
	p = &node{}
	p = (nil)
	if p == nil && q == nil && retNil() == nil {
		r += 1000000
	}
	s := []*node{(nil)}
	m := map[string]*node{"a": (nil)}
	ch := make(chan *node, 1)
	ch <- (nil)
	rv := <-ch
	if s[0] == nil && m["a"] == nil && rv == nil {
		r += 10000000
	}
	m["b"] = (nil)
	if len(m) == 2 {
		r += 100000000
	}
	return r // 111101111
}

func parenNilPanic() int {
	panic((nil))
}

func main() {
	println("nilLeftRoutes", nilLeftRoutes())
	println("nilLeftBoxedAndAssert", nilLeftBoxedAndAssert())
	println("parenNilSinks", parenNilSinks())
	func() {
		defer func() { r := recover(); println("parenNilPanic", "panic:", r.(error).Error()) }()
		println("parenNilPanic", parenNilPanic())
	}()
}
