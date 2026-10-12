package main

// Seeded-heap slice C: a nil-terminated list in the seed (cell 2's next is the
// seed value {"nil":true}) and a nil ARGUMENT (--arg-nil). `walk` counts the
// nodes and sums their values; `nil-arg` passes nil (0 nodes); `nil-deref`
// reads past the list's end — the Go panic, no seed key on either side.

type Node struct {
	next *Node
	val  int
}

func walk(n *Node) int {
	k, s := 0, 0
	for n != nil {
		k++
		s += n.val
		n = n.next
	}
	return k*100 + s
}

func third(n *Node) int {
	return n.next.next.next.val
}

func main() {
	var c0, c1, c2 Node
	c0 = Node{next: &c1, val: 1}
	c1 = Node{next: &c2, val: 2}
	c2 = Node{next: nil, val: 3}
	println(walk(&c0), walk(nil))
	println(third(&c0))
}
