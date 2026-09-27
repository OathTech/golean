package main

type S struct{ xs [0]int }

func readZero(i int) (r int) {
	defer func() {
		if recover() != nil {
			r = 100
		}
	}()
	var a [0]int
	return a[i]
}

func elemAddr(i int) (r int) {
	defer func() {
		if recover() != nil {
			r = 200
		}
	}()
	var a [3]int
	p := &a[i]
	return *p
}

func fieldElem(i int) (r int) {
	defer func() {
		if recover() != nil {
			r = 300
		}
	}()
	var s S
	q := &s
	return q.xs[i]
}

func rangeAddr() (r int) {
	var a [3]int
	for i := range a {
		p := &a[i]
		*p = i + 1
		r += *p
	}
	return r
}

func F() (int, int, int, int) {
	i := 5
	return readZero(i), elemAddr(i), fieldElem(i), rangeAddr()
}

func main() {
	a, b, c, d := F()
	println(a, b, c, d)
}
