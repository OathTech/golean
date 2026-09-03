package main

import "fmt"

type Inner struct{ v int }

func (i Inner) Val() int { return i.v }

type Valuer interface{ Val() int }

//go:noinline
func call(v Valuer) int { return v.Val() }

var global Valuer

func try(name string, f func()) {
	defer func() { fmt.Println(name, "->", recover()) }()
	f()
}

func main() {
	var p *Inner
	try("direct", func() { var v Valuer = p; _ = v.Val() })
	try("methodvalue", func() { var v Valuer = p; f := v.Val; _ = f() })
	try("noinline-param", func() { _ = call(p) })
	global = p
	try("global-iface", func() { _ = global.Val() })
	try("direct-ptr-methodvalue", func() { f := p.Val; _ = f() })
	try("methodexpr", func() { f := (*Inner).Val; _ = f(p) })
	try("ptr-call", func() { _ = p.Val() })
}
