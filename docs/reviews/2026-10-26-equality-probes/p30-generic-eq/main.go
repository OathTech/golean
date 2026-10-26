package main

func main() { run() }

func eq[T comparable](a, b T) bool { return a == b }
func ne[T comparable](a, b T) bool { return a != b }
func lt[T int | float64 | string](a, b T) bool { return a < b }
func isNil[T any](v T) bool { return any(v) == nil }
func find[T comparable](xs []T, x T) int {
	for i, y := range xs {
		if y == x {
			return i
		}
	}
	return -1
}

type Pair[T any] struct{ A, B T }
type tagA struct {
	X int `json:"a"`
}
type tagB struct {
	X int `json:"b"`
}

func try(name string, f func() bool) {
	defer func() {
		if r := recover(); r != nil {
			println(name, "panic")
		}
	}()
	println(name, f())
}

func run() {
	zero := 0.0
	nan := zero / zero
	println(eq(1, 1), eq(nan, nan), ne(nan, nan), eq(-zero, zero), eq("a", "a"), eq[any](1, int64(1)), eq[any](1, 1))
	println(lt(nan, 1.0), lt(1, 2), lt("a", "b"), lt(-zero, zero))
	x := 1
	a := tagA{7}
	b := (*tagB)(&a)
	println(eq(&x, &x), eq(&a.X, &b.X), eq[any](&a.X, &b.X), eq[any](&a, b))
	println(eq(Pair[int]{1, 2}, Pair[int]{1, 2}), eq(Pair[float64]{nan, 0}, Pair[float64]{nan, 0}), eq[any](Pair[int]{}, Pair[int64]{}), eq[any](Pair[int]{}, Pair[int]{}))
	var np *int
	println(isNil(np), isNil[any](nil), isNil(0), isNil[error](nil))
	println(find([]float64{1, nan, 2}, nan), find([]string{"a", "b"}, "b"), find[any]([]any{1, "a", int64(2)}, int64(2)), find[any]([]any{1, "a"}, nil))
	try("generic-any-slice", func() bool { return eq[any]([]int{}, []int{}) })
	try("generic-any-struct-slice", func() bool { return eq[any](Pair[[]int]{}, Pair[[]int]{}) })
	m := map[Pair[int]]int{}
	m[Pair[int]{1, 2}] = 1
	m[Pair[int]{1, 2}] = 2
	println(len(m), m[Pair[int]{1, 2}])
	var i1 any = Pair[int]{1, 2}
	switch i1.(type) {
	case Pair[int64]:
		println("Pair[int64]")
	case Pair[int]:
		println("Pair[int]")
	}
}
