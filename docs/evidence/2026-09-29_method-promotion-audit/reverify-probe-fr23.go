package main

import "iter"

type In struct{ n int }

func (i In) All() iter.Seq[int] { return nil }
func (i In) Take(s iter.Seq[int]) int { return i.n }

type A interface{ All() iter.Seq[int] }
type T interface{ Take(iter.Seq[int]) int }

type S struct {
	*In
	z int
}

func discard() int {
	var p *S
	var a A = p
	a.All()
	return 0
}

func takeNil() int {
	var p *S
	var t T = p
	return t.Take(nil)
}

func viaOther() int {
	var p *S
	var t T = p
	_ = t
	return 1
}

func main() {}
