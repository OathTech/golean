package main

// spec#Type_definitions block Type_definitions-2-15b8a5c5: a type definition
// creates a DISTINCT type — Point differs from struct{ x, y float64 } and
// polar differs from Point (conversion, not plain assignment, moves values
// across); TreeNode is self-referential through *TreeNode; Block is a normal
// interface declaration usable as a type.

type (
	Point struct{ x, y float64 } // Point and struct{ x, y float64 } are different types
	polar Point                  // polar and Point denote different types
)

type TreeNode struct {
	left, right *TreeNode
	value       any
}

type Block interface {
	BlockSize() int
	Encrypt(src, dst []byte)
	Decrypt(src, dst []byte)
}

func typeDefinitionsDistinct() int {
	p := Point{1.5, 2.5}
	q := polar(p) // distinct types with identical underlying type: convertible
	var anon struct{ x, y float64 } = struct{ x, y float64 }{4, 5}
	p2 := Point(anon) // ... same for the unnamed struct type
	root := TreeNode{value: 7}
	root.left = &TreeNode{value: 3}
	n := root.value.(int)*10 + root.left.value.(int) // 73
	var blk Block                                    // interface type: zero value nil
	if blk != nil {
		return -1
	}
	return n + int(q.x+q.y+p2.x) // 73 + 4 + 4 = 81
}
