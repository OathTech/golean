package main

import "fmt"

var w int

func wit(x int) int { w = w*31 + 5; return x }

// E13 consistency probes (fr27-fr28 audit fix round): the make guard
// refuses `iv.(int) + len(make([]int, t[k]))`; these are the same shape
// with the OTHER always-hoisting constructs.
func appendShape() int {
	var iv interface{} = "s"
	s := []int{1}
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(append(s, t[k])) + wit(5)
}

func copyShape() int {
	var iv interface{} = "s"
	dst := []int{1, 2, 3}
	src := []int{9}
	t := []int{1, 2}
	k := 5
	return iv.(int) + copy(dst[t[k]:], src)
}

func makeShape() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + len(make([]int, t[k]))
}

func minShape() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + min(t[k], 1) + wit(5)
}

func callShape() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + wit(t[k])
}

func run(name string, f func() int) {
	defer func() { fmt.Printf("%s|gc|%v\n", name, recover()) }()
	f()
}

func main() {
	run("appendShape", appendShape)
	run("copyShape", copyShape)
	run("makeShape", makeShape)
	run("minShape", minShape)
	run("callShape", callShape)
}
