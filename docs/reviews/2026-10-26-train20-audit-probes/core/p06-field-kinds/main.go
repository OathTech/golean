package main

// Fields of map, slice, func, chan, interface, error, array-of-struct and
// pointer types: the wire's FieldDef equality over every Ty constructor.
type In struct{ V int }
type A struct {
	M   map[string]int
	S   []int
	F   func(int) int
	C   chan int
	I   any
	E   error
	Arr [2]In
	P   *In
}
type B struct {
	M   map[string]int
	S   []int
	F   func(int) int
	C   chan int
	I   any
	E   error
	Arr [2]In
	P   *In
}

func probe() int {
	n := In{7}
	a := A{M: map[string]int{"k": 1}, S: []int{2, 3}, F: func(x int) int { return x + 1 }, C: make(chan int, 1), I: 4, Arr: [2]In{{5}, {6}}, P: &n}
	pb := (*B)(&a)
	x := *pb
	x.C <- 9
	r := x.M["k"]*100000 + len(x.S)*10000 + x.F(2)*1000 + (<-a.C)*100 + x.Arr[1].V*10 + x.P.V
	if x.I == any(4) && x.E == nil {
		return r
	}
	return -r
}

func main() { println(probe()) }
