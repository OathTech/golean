package main

func main() { run() }

type A struct{ X, Y int }
type B struct{ X, Y int }

func run() {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	println(a.X == 9, a.Y == 9, pb.Y == 9, &a.X == &pb.X)
	m := map[*int]int{&a.X: 1}
	println(m[&pb.X])
}
