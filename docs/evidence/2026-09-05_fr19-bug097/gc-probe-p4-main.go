package main

import (
	"fmt"
	ri "red/inner"
)

type Pair[A, B any] struct {
	a A
	b B
}

type box[T any] struct{ v T }

func (b box[T]) m() {}

func fA() any { type score int; return box[score]{} }
func fB() any { type other int; return box[other]{} }
func fC() any { type score int; return box[score]{} }
func fD() any { type score int; return score(0) }

func gen[T any](x T) any { type inner struct{ v T }; return inner{x} }

type S struct{ X int }

func main() {
	fmt.Printf("%T\n", Pair[int, string]{})
	fmt.Printf("%T\n", Pair[ri.T, *ri.Q]{})
	fmt.Printf("%T\n", Pair[interface{ Get() ri.T }, struct{ X int }]{})
	fmt.Printf("%T\n", Pair[[]ri.T, map[string]ri.T]{})
	fmt.Printf("%T\n", Pair[func(ri.T) bool, chan ri.T]{})
	fmt.Printf("%T\n", Pair[any, error]{})
	fmt.Printf("%T %T %T %T\n", fA(), fB(), fC(), fD())
	fmt.Printf("%T %T\n", gen(1), gen("s"))
	var e any = struct {
		S
		X int `json:"x"`
		y ri.T
	}{}
	fmt.Printf("%T\n", e)
	var g any = struct{}{}
	fmt.Printf("%T\n", g)
	var h any = [3]ri.T{}
	fmt.Printf("%T\n", h)
	var i any = func(...int) (int, error) { return 0, nil }
	fmt.Printf("%T\n", i)
	var j any = (chan<- ri.T)(nil)
	var k any = (<-chan ri.T)(nil)
	fmt.Printf("%T %T\n", j, k)
	var l any = interface{ Get() ri.T }(nil)
	fmt.Printf("%T %v\n", l, l)
	var m any = []interface {
		Get() ri.T
		get() int
	}{}
	fmt.Printf("%T\n", m)
	var n any = [][]struct{ A, B int }{}
	fmt.Printf("%T\n", n)
	var o any = map[struct{ K string }][]byte{}
	fmt.Printf("%T\n", o)
	var p any = uint8(1)
	var q any = rune(1)
	fmt.Printf("%T %T\n", p, q)
	defer func() { fmt.Println(recover()) }()
	var r any = box[int]{}
	_ = r.(box[string])
}
