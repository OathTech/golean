// noodler probe — a panic in init() aborts before main runs
// (spec#Package_initialization, spec#Program_execution).
package main

var seen = 0

func init() {
	seen = 1
	panic("init-boom")
}

func afterInit() int { return seen }

func main() {}
