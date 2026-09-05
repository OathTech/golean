package main

type A [2]int
type B [2]int
type Alias = A
func NamedIdentity() int {
 x := [2]int{2, 3}
 a := A(x)
 b := B(Alias(a))
 b[0] = 5
 var boxed any = b
 _, right := boxed.(B)
 _, wrong := boxed.(A)
 if !right || wrong { return -1 }
 return x[0]*100 + a[0]*10 + b[0]
}
type IA [2]any
type IB [2]any
func InterfaceElements() int {
 var p *int
 x := IA{p, A{2, 3}}
 y := IB(x)
 y[1] = A{4, 5}
 if y[0] == nil { return -1 }
 q, ok := y[0].(*int)
 if !ok || q != nil { return -2 }
 return x[1].(A)[0]*10 + y[1].(A)[0]
}
type Ref struct { m map[int]int; f func() int; c chan int }
type RA [1]Ref
type RB [1]Ref
func OtherReferences() int {
 n := 2
 x := RA{{map[int]int{0:3}, func() int { return n }, make(chan int,1)}}
 y := RB(x)
 y[0].m[0] = 4
 n = 5
 y[0].c <- 6
 v := <-x[0].c
 y[0].m = map[int]int{0:7}
 return x[0].m[0]*1000 + y[0].m[0]*100 + y[0].f()*10 + v
}
type Rec [1]*Rec
type RecCopy [1]*Rec
func RecursiveReferences() int {
 var x Rec
 x[0] = &x
 y := RecCopy(x)
 if y[0] != &x || (*y[0])[0] != &x { return -1 }
 y[0] = nil
 if x[0] != &x { return -2 }
 return 1
}
type EF [0]func() int
type EG [0]func() int
func EmptyFunctions() int {
 x := EF{}
 y := EG(x)
 return len(y)
}
func main() {}
