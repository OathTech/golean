package main

import "maps"

func main() { run() }

func run() {
	println(maps.Equal(map[int]int{1: 1}, map[int]int{1: 1}))
}
