package main

type nilDispatchNode struct {
	next *nilDispatchNode
}

func (n *nilDispatchNode) Size() int {
	if n == nil {
		return 0
	}
	return 1 + n.next.Size()
}

func nilReceiverInterfaceDispatch() int {
	var n *nilDispatchNode
	var x interface{ Size() int } = n
	score := 0
	if x != nil {
		score += 1
	}
	return score + x.Size()*10
}

func main() {
	nilReceiverInterfaceDispatch()
}
