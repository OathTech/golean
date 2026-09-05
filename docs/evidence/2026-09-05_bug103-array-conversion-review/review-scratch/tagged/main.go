package main
func TaggedArray() int {
 x := [1]struct { X int `a` }{{3}}
 y := [1]struct { X int `b` }(x)
 y[0].X = 4
 return x[0].X*10+y[0].X
}
func main() { println(TaggedArray()) }
