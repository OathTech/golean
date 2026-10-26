package main

import "sub"

// The positive half: the conversion inside sub between two of its own types
// (unexported field in one package: identical), dereferenced whole here.
type C struct {
	x int
	Y int
}

func probe() int {
	pa := sub.MkA()
	pb := sub.Conv(pa)
	v := *pb
	r := v.Sum()*10 + sub.Peek(pa)
	var i any = *pb
	if _, ok := i.(sub.B); ok {
		r += 100
	}
	return r
}

func main() { println(probe()) }
