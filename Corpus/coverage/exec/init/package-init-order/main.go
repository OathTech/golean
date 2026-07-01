package main

var derived = base + 1
var base = 10
var initFlag int

func init() {
	initFlag = 100
}

func packageInitOrder() int {
	return derived + initFlag
}
