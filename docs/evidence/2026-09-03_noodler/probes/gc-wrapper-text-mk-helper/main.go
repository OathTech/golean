package main

import "fmt"

type Inner struct{ v int }

func (i Inner) Val() int { return i.v }

type Valuer interface{ Val() int }

func mk(p *Inner) Valuer { return p }

func try(name string, f func()) {
	defer func() { fmt.Println(name, "->", recover()) }()
	f()
}

func main() {
	var p *Inner
	try("mk-helper", func() { v := mk(p); _ = v.Val() })
}
