// E8 probe: multi-file declaration order. za.go and zb.go each declare
// one package-level var whose initializer records itself; both are
// dependency-free, so init order = declaration order = the order the
// files are presented to the compiler.
package main

var seq string

func rec(s string) int {
	seq += s
	return len(seq)
}

func main() {
	println(seq)
}
