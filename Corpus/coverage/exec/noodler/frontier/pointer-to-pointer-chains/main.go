// noodler frontier probe — **pp compound assignment and (*pn).field.method chains
package main

type Node struct {
	v    int
	next *Node
}

func (n *Node) Val() int { return n.v }

// Pointer-to-pointer dereference chains and compound assignment through
// a double deref.
func pointerToPointerChains() int {
	x := 1
	p := &x
	pp := &p
	**pp += 5
	n := &Node{v: 2, next: &Node{v: 3}}
	pn := &n
	(*pn).next.v++
	return x*100 + (*pn).Val()*10 + n.next.Val()
}

func main() {}
