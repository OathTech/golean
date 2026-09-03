package main

import (
	"fmt"
	"os"
)

type Inner struct{ v int }

func (i Inner) Val() int { return i.v }

type Valuer interface{ Val() int }

//go:noinline
func mk(p *Inner) Valuer { return p }

var global Valuer

//go:noinline
func spawnParam(v Valuer) { go v.Val() }

func main() {
	var p *Inner
	shape := os.Args[1]
	switch shape {
	case "same-fn":
		var v Valuer = p
		go v.Val()
	case "opaque":
		v := mk(p)
		go v.Val()
	case "global":
		global = p
		go global.Val()
	case "param":
		spawnParam(p)
	case "methodvalue":
		v := mk(p)
		f := v.Val
		go f()
	case "closure":
		v := mk(p)
		go func() { v.Val() }()
	}
	select {}
	fmt.Println("unreachable")
}
