package main

// Seeded-heap slice C: a two-cell CYCLE (cell 0 -> cell 1 -> cell 0; design §0
// P1's sum2 shape). `next-ptr` returns a pointer INTO the seed, observed
// seed-relative (`seedRef` cell 1, path []), and the seed key carries the cycle
// itself; `relink` rewires cell 1 to itself and bumps both values — the seed
// key shows the mutated cells, pointers included.

type Node struct {
	next *Node
	val  int
}

func next(n *Node) *Node {
	return n.next
}

func relink(n *Node) int {
	m := n.next
	m.next = m
	n.val = n.val * 10
	m.val++
	return n.val + m.val
}

func main() {
	var c0, c1 Node
	c0 = Node{next: &c1, val: 2}
	c1 = Node{next: &c0, val: 3}
	println(next(&c0) == &c1, relink(&c0), c1.next == &c1)
}
