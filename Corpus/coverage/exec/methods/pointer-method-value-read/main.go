package main

type ptrBox struct {
	n int
}

func (b *ptrBox) load(dst *int) {
	*dst = b.n
}

func pointerMethodValueRead() int {
	b := &ptrBox{n: 4}
	f := b.load
	r := 0
	f(&r)
	return r * 11
}

func main() {
	pointerMethodValueRead()
}
