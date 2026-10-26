package main

import (
	"reflect"
	"sort"
)

func main() { run() }

func run() {
	println(reflect.DeepEqual([]int{1}, []int{1}))
	xs := []int{3, 1}
	sort.Ints(xs)
	println(xs[0])
}
