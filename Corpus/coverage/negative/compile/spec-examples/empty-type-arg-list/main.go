// spec#Instantiations block Instantiations-3-8fe1b1b6: apply[] illegal: a partial type argument list cannot be empty
package main

func apply[S ~[]E, E any](s S, f func(E) E) S { return s }

func main() {
	f0 := apply[] // illegal: type argument list cannot be empty
	_ = f0
}
