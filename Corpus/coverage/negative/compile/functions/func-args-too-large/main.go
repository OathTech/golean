package main

// The function type's argument area (TFUNCARGS: params, rounded to 8,
// then results) reaches MaxWidth (1<<50); gc go1.26.5 reports it as an
// internal compiler error.
func main() {
	var f func(a [1 << 49]byte) (r [1 << 49]byte)
	println(f == nil)
}
