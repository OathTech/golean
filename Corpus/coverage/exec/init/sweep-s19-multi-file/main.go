package main

var tr int

func mark(x int) int { tr = tr*10 + x; return x }

var b3m = mark(1)

func init() { mark(6) }

// threeFileOrder: schedule b(3) m(1) a(2), inits 4 5 6 → trace 312456;
// a = 10 + 2.
func threeFileOrder() int { return tr*100 + b3a + b3b - 3 }

func main() { println(threeFileOrder()) }
