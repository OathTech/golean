package main

func main() { run() }

type A struct{ X, Y int }
type B struct{ X, Y int }
type In struct{ V int }
type OA struct {
	I In
	N int
}
type OB struct {
	I In
	N int
}

func run() {
	as := []A{{1, 2}}
	pb := (*B)(&as[0])
	println(*pb == B{1, 2})
}
