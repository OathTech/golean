package main

import (
	"fmt"
	"probe087/sub"
)

type Inner struct{ v int }

func (i Inner) Val() int { return i.v }

type Valuer interface{ Val() int }

// Promotion by VALUE embedding: *Outer nil box.
type OuterV struct{ Inner }

// Promotion by POINTER embedding: *OuterP nil box, and OuterP value with nil *Inner.
type OuterP struct{ *Inner }

// Named non-struct receiver.
type MyInt int

func (m MyInt) Val() int { return int(m) }

// Generic receiver.
type Box[T any] struct{ x T }

func (b Box[T]) Val() int { return 1 }

//go:noinline
func call(v Valuer) int { return v.Val() }

func try(name string, f func()) {
	defer func() {
		r := recover()
		_, isRE := r.(interface{ RuntimeError() })
		fmt.Printf("%-28s -> %v   [runtime.Error=%v]\n", name, r, isRE)
	}()
	f()
}

func main() {
	var p *Inner
	var s *sub.T
	var ov *OuterV
	var op *OuterP
	var mi *MyInt
	var bx *Box[int]
	try("main-noinline", func() { _ = call(p) })
	try("main-direct", func() { var v Valuer = p; _ = v.Val() })
	try("sub-pkg-noinline", func() { _ = call(s) })
	try("sub-pkg-direct", func() { var v Valuer = s; _ = v.Val() })
	try("promoted-valembed-ptrbox", func() { _ = call(ov) })
	try("promoted-ptrembed-ptrbox", func() { _ = call(op) })
	try("promoted-ptrembed-valbox", func() { _ = call(OuterP{}) })
	try("named-nonstruct-noinline", func() { _ = call(mi) })
	try("generic-noinline", func() { _ = call(bx) })
	try("methodvalue-iface", func() { var v Valuer = p; f := v.Val; _ = f() })
	try("spawn", func() {
		done := make(chan any)
		var v Valuer = p
		go func() {
			defer func() { done <- recover() }()
			v.Val()
		}()
		r := <-done
		_, isRE := r.(interface{ RuntimeError() })
		fmt.Printf("%-28s -> %v   [runtime.Error=%v]\n", "spawn(child recover)", r, isRE)
	})
}
