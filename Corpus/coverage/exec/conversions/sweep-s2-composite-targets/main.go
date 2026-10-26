package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Slice / map / func / pointer targets past BUG-020's rows: the conversion
// result sliced, ranged, appended, indexed, written through (aliasing), a method
// value and a func literal converted to a func type, every defined-type nil,
// and defined types over []any and over maps of structs.

type MyInts []int
type MyMap map[string]int
type MyFn func() int
type MyChan chan int
type P *int
type T struct{ n int }
type A struct{ X int }
type Args []any
type M1 map[string]A
type M2 map[string]A

func (t T) Get() int { return t.n }

func sliceIdioms() (int, int, int, int) {
	xs := []int{1, 2, 3, 4}
	tail := MyInts(xs)[1:]
	n := len(MyInts(xs))
	sum := 0
	for _, v := range MyInts(xs) {
		sum += v
	}
	ys := append(MyInts(nil), MyInts(xs)...)
	tail[0] = 20
	return len(tail), n, sum, xs[1] + ys[1]
}

func mapIdioms() (int, int) {
	m := map[string]int{"a": 1}
	v := MyMap(m)["a"]
	MyMap(m)["b"] = 2
	delete(MyMap(m), "a")
	return v, len(m)*10 + m["b"]
}

func methodValueToFuncType() int {
	t := T{5}
	f := (func() int)(t.Get)
	g := MyFn(t.Get)
	t.n = 6
	return f()*10 + g()
}

func funcLiteralConverted() int {
	return MyFn(func() int { return 3 })() + (func() int)(func() int { return 4 })()
}

func definedNils() int {
	var r int
	if MyInts(nil) == nil {
		r += 1
	}
	if MyMap(nil) == nil {
		r += 10
	}
	if MyFn(nil) == nil {
		r += 100
	}
	if MyChan(nil) == nil {
		r += 1000
	}
	if P(nil) == nil {
		r += 10000
	}
	if (chan int)(nil) == nil {
		r += 100000
	}
	x := MyInts(nil)
	x = append(x, 1)
	m := MyMap(nil)
	return r + len(x) + len(m)
}

func anySliceAndStructMaps() int {
	args := Args([]any{1, "ab", A{3}})
	m := M1{"k": {4}}
	n := M2(m)
	n["j"] = A{5}
	r := 0
	if v, ok := args[0].(int); ok {
		r += v
	}
	if v, ok := args[1].(string); ok {
		r += len(v) * 10
	}
	if v, ok := args[2].(A); ok {
		r += v.X * 100
	}
	return r*100 + len(m)*10 + m["j"].X
}

func main() {}
