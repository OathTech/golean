package main

type tree struct {
	v     int
	left  *tree
	right *tree
}

func (t *tree) size() int {
	if t == nil {
		return 0
	}
	return 1 + t.left.size() + t.right.size()
}

func nilReceiver() int {
	var t *tree
	full := &tree{v: 1, left: &tree{v: 2}, right: &tree{v: 3}}
	return t.size()*100 + full.size()
}
