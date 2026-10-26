package main

func main() { run() }

type A int
type B int
type C = A

type I1 interface{ M() }
type I2 interface{ M() }

func (A) M() {}

type Str struct{}

func (Str) String() string { return "s" }

type Stringer interface{ String() string }
type Stringer2 interface{ String() string }

func kind(v any) string {
	switch v.(type) {
	case int:
		return "int"
	case A:
		return "A"
	case B:
		return "B"
	case nil:
		return "nil"
	case I1:
		return "I1"
	case error:
		return "error"
	case []int:
		return "[]int"
	case [2]int:
		return "[2]int"
	case *int:
		return "*int"
	case func():
		return "func()"
	case map[string]int:
		return "map"
	case chan int:
		return "chan int"
	case <-chan int:
		return "<-chan int"
	}
	return "other"
}

func run() {
	var ni any
	var np *int
	ch := make(chan int)
	println(kind(1), kind(A(1)), kind(B(1)), kind(C(1)), kind(ni), kind(np), kind([]int{}), kind([2]int{}), kind(func() {}), kind(map[string]int{}), kind(ch), kind((<-chan int)(ch)), kind(int64(1)), kind(Str{}))
	var v any = B(3)
	if _, ok := v.(A); ok {
		println("B asserted as A")
	} else {
		println("B is not A")
	}
	if a, ok := v.(B); ok {
		println("B is B", int(a))
	}
	if _, ok := v.(I1); ok {
		println("B satisfies I1")
	} else {
		println("B does not satisfy I1")
	}
	var w any = A(4)
	if i, ok := w.(I2); ok {
		i.M()
		println("A satisfies I2")
	}
	if _, ok := w.(C); ok {
		println("A asserted as alias C")
	}
	switch x := v.(type) {
	case A, B:
		println("multi-case binds iface, is B:", func() bool { _, ok := x.(B); return ok }())
	}
	var s any = Str{}
	switch s.(type) {
	case Stringer2:
		println("Stringer2 first")
	case Stringer:
		println("Stringer second")
	}
	// type assertion panic texts on mismatch
	defer func() {
		if r := recover(); r != nil {
			if e, ok := r.(error); ok {
				println("panic:", e.Error())
			}
		}
	}()
	_ = v.(A)
}
