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
	o := OA{In{1}, 2}
	pb := (*OB)(&o)
	println(pb.I == In{1}, *pb == OB{In{1}, 2})
}
