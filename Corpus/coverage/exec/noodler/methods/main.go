// noodler probes — methods on non-struct types (func, array, slice,
// map, channel, string, bool) and method-set edges (spec#Method_declarations,
// spec#Method_sets, spec#Method_values, spec#Method_expressions).
package main

// Method on a function type.
type IntFn func(int) int

func (f IntFn) Twice(x int) int { return f(f(x)) }

func methodOnFuncType() int {
	inc := IntFn(func(x int) int { return x + 1 })
	return inc.Twice(5)
}

// Method on an array type (value receiver copies; pointer receiver
// mutates).
type Vec [3]int

func (v Vec) Sum() int {
	s := 0
	for _, x := range v {
		s += x
	}
	return s
}
func (v *Vec) Scale(k int) {
	for i := range v {
		v[i] *= k
	}
}
func (v Vec) SetFirst() Vec { v[0] = 100; return v }

func methodsOnArrayType() (int, int, int) {
	v := Vec{1, 2, 3}
	v.Scale(2)
	w := v.SetFirst()
	return v.Sum(), w[0], v[0]
}

// Method on a slice type: value receiver append does not affect caller.
type Ints []int

func (s Ints) AppendCopy(x int) int { s = append(s, x); return len(s) }
func (s *Ints) Append(x int)        { *s = append(*s, x) }
func (s Ints) Set0(x int)           { s[0] = x }

func methodsOnSliceType() (int, int, int) {
	s := Ints{1, 2}
	n := s.AppendCopy(3)
	s.Append(4)
	s.Set0(9)
	return n, len(s), s[0]
}

// Method on a channel type.
type Pipe chan int

func (p Pipe) Put(x int) { p <- x }
func (p Pipe) Get() int  { return <-p }

func methodOnChannelType() int {
	p := make(Pipe, 1)
	p.Put(6)
	return p.Get()
}

// Method on a string type and a bool type.
type Word string

func (w Word) Shout() string { return string(w) + "!" }

type Flag bool

func (f Flag) Not() Flag { return !f }

func methodsOnStringAndBool() (string, bool) {
	return Word("hi").Shout(), bool(Flag(true).Not())
}

// Method value bound to a value receiver copies at evaluation; bound to
// a pointer receiver stays live.
type Counter struct{ n int }

func (c Counter) Get() int { return c.n }
func (c *Counter) Inc()    { c.n++ }

func methodValueBindingTime() (int, int) {
	c := Counter{1}
	get := c.Get
	inc := c.Inc
	c.n = 10
	inc()
	return get(), c.n
}

// Method expressions with value and pointer receivers.
func methodExpressions() (int, int) {
	c := Counter{3}
	get := Counter.Get
	inc := (*Counter).Inc
	inc(&c)
	return get(c), c.n
}

// Method on a map type mutating the shared map.
type Tally map[string]int

func (t Tally) Add(k string) { t[k]++ }

func methodOnMapType() int {
	t := Tally{}
	t.Add("a")
	t.Add("a")
	t.Add("b")
	return t["a"]*10 + t["b"]
}

// Interface satisfied by a func type with a method.
type Runner interface{ Run() int }

type RunFn func() int

func (f RunFn) Run() int { return f() }

func funcTypeSatisfiesInterface() int {
	var r Runner = RunFn(func() int { return 42 })
	return r.Run()
}

// Pointer-receiver method through an addressable array element and a
// slice element.
func pointerReceiverThroughElements() (int, int) {
	arr := [2]Counter{}
	sl := []Counter{{}, {}}
	arr[1].Inc()
	arr[1].Inc()
	sl[0].Inc()
	return arr[1].n, sl[0].n
}

// Pointer-receiver method through a map element is not allowed; a
// value-receiver method IS. (Value receiver only here.)
func valueReceiverThroughMapElement() int {
	m := map[int]Counter{1: {5}}
	return m[1].Get()
}

// Method call on a struct literal (addressable? no) with a value
// receiver, and on &literal with a pointer receiver.
func methodsOnLiterals() int {
	a := Counter{2}.Get()
	p := &Counter{3}
	p.Inc()
	return a*10 + p.n
}

// Embedding a defined non-struct type with methods promotes them.
type Wrapper struct {
	Word
	extra int
}

func promotedFromNonStructEmbedded() string {
	w := Wrapper{Word("yo"), 1}
	return w.Shout()
}

// Shadowing a promoted method with the outer type's own method.
type Loud struct{ Word }

func (l Loud) Shout() string { return string(l.Word) + "!!!" }

func outerMethodShadowsPromoted() (string, string) {
	l := Loud{"hey"}
	return l.Shout(), l.Word.Shout()
}

// Two embedded types with the same method at the same depth: calling
// via an explicit path avoids ambiguity.
type A struct{}
type B struct{}

func (A) Name() string { return "A" }
func (B) Name() string { return "B" }

type AB struct {
	A
	B
}

func explicitPathAvoidsAmbiguity() string {
	ab := AB{}
	return ab.A.Name() + ab.B.Name()
}

// Depth rule: the shallower method wins over a deeper one.
type Deep struct{ A }
type Shallow struct {
	Deep
	B
}

func shallowerMethodWins() string {
	return Shallow{}.Name()
}

// Method value from an interface holding a value type.
func methodValueFromInterface() int {
	var r Runner = RunFn(func() int { return 5 })
	f := r.Run
	return f() * 2
}

// Recursive method on a pointer type with nil base case.
type Tree struct {
	l, r *Tree
	v    int
}

func (t *Tree) Sum() int {
	if t == nil {
		return 0
	}
	return t.v + t.l.Sum() + t.r.Sum()
}

func nilReceiverRecursion() int {
	t := &Tree{&Tree{nil, nil, 1}, &Tree{&Tree{nil, nil, 2}, nil, 3}, 4}
	return t.Sum()
}

func main() {}
