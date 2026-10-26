package main

// Train-19 shake probes for DC03's local space: the seed budget is judged per
// cell type (dimensions against sliceCapBudget, footprint against
// arrayFootprintBudget) BEFORE any allocation. Big is 16M+1 leaves through a
// declared struct (over the footprint budget via the table walk); Mid is 4M.

type Big struct {
	A [8388608]int
	B [8388608]int
	C [1]int
}

// Mid2 is decoder-admitted (65536 per dimension, 4M leaves); [4]Mid2 is 16M+ leaves.
type Mid2 struct {
	A [65536][64]int
}

func mid2Nil(p *Mid2) bool { return p == nil }

type Node struct {
	next *Node
	val  int
}

func isNil(p *int) bool { return p == nil }

func bigNil(p *Big) bool { return p == nil }

func cycleLen(n *Node) int {
	c := 0
	for p := n; ; p = p.next {
		c++
		if p.next == n {
			return c
		}
	}
}

func main() {
	println(isNil(nil), bigNil(nil))
}
