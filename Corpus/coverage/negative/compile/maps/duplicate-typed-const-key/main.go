package main

type key int

const k key = 1

var _ = map[key]int{
	k: 1,
	1: 2,
}
