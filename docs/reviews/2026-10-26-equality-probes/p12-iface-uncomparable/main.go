package main

func main() { run() }

type S struct {
	I any
}

type WithSlice struct {
	S []int
}

type WithFunc struct{ F func() }

func try(name string, f func() bool) {
	defer func() {
		if r := recover(); r != nil {
			println(name, "panic")
		}
	}()
	println(name, f())
}

func run() {
	try("slice", func() bool { return any([]int{}) == any([]int{}) })
	try("slice-neq", func() bool { return any([]int{}) != any([]int{}) })
	try("map", func() bool { return any(map[int]int{}) == any(map[int]int{}) })
	try("func", func() bool { return any(func() {}) == any(func() {}) })
	try("slice-vs-int", func() bool { return any([]int{}) == any(1) })
	try("slice-vs-nil", func() bool { return any([]int{}) == nil })
	try("nilslice-vs-nilslice", func() bool { return any([]int(nil)) == any([]int(nil)) })
	try("struct-with-slice", func() bool { return any(WithSlice{}) == any(WithSlice{}) })
	try("array-of-slice", func() bool { return any([1][]int{}) == any([1][]int{}) })
	try("struct-with-func", func() bool { return any(WithFunc{}) == any(WithFunc{}) })
	try("struct-iface-field-slice", func() bool { return S{[]int{}} == S{[]int{}} })
	try("struct-iface-field-diff", func() bool { return S{[]int{}} == S{1} })
	try("struct-iface-field-ok", func() bool { return S{1} == S{1} })
	try("array-iface-elem", func() bool { return [1]any{[]int{}} == [1]any{[]int{}} })
	try("array-iface-elem-short", func() bool { return [2]any{1, []int{}} == [2]any{2, []int{}} })
	try("array-iface-elem-reach", func() bool { return [2]any{1, []int{}} == [2]any{1, []int{}} })
	try("switch-iface-slice", func() bool {
		var v any = []int{}
		switch v {
		case 1:
			return false
		}
		return true
	})
	try("switch-iface-slice-case", func() bool {
		var v any = 1
		switch v {
		case any([]int{}):
			return false
		}
		return true
	})
	type Named []int
	try("named-slice", func() bool { return any(Named{}) == any(Named{}) })
	type NamedS struct{ X []int }
	try("named-struct-slice", func() bool { return any(NamedS{}) == any(NamedS{}) })
	try("iface-in-iface", func() bool {
		var a any = []int{}
		var b any = a
		return a == b
	})
	try("error-iface-slice", func() bool {
		var a any = []int{}
		var e error
		return a == e
	})
}
