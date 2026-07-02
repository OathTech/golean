package main

type methodValueNode struct {
	next *methodValueNode
}

func (n *methodValueNode) size() int {
	if n == nil {
		return 0
	}
	return 1 + n.next.size()
}

func nilPointerMethodValue() int {
	var n *methodValueNode
	f := n.size
	return f()
}

func main() {
	nilPointerMethodValue()
}
