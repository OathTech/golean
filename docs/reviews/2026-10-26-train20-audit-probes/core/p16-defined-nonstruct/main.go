package main

// Control: a converted pointer to a defined NON-struct type; derefRetag's
// resolve yields a plain body and must leave the value alone; the box's
// dynamic type is the static one.
type MyInt int
type YourInt int

func probe() int {
	n := MyInt(5)
	py := (*YourInt)(&n)
	var i any = *py
	r := 0
	switch i.(type) {
	case MyInt:
		r = 1
	case YourInt:
		r = 2
	}
	*py = 7
	return r*10 + int(n)
}

func main() { println(probe()) }
