package main

func main() { run() }

type MyInt int

func try(name string, f func() int) {
	defer func() {
		if r := recover(); r != nil {
			println(name, "panic")
		}
	}()
	println(name, f())
}

func run() {
	m := map[any]int{}
	m[1] = 1
	m[int64(1)] = 2
	m["1"] = 3
	m[1.0] = 4
	m[MyInt(1)] = 5
	m[nil] = 6
	m[true] = 7
	m[[2]int{1, 1}] = 8
	m[struct{}{}] = 9
	println(len(m), m[1], m[int64(1)], m["1"], m[1.0], m[MyInt(1)], m[nil], m[true], m[[2]int{1, 1}], m[struct{}{}])
	m[1] = 10
	println(len(m), m[1])
	delete(m, int32(1))
	println(len(m))
	delete(m, 1)
	println(len(m), m[1])
	try("insert-slice", func() int { m[[]int{}] = 1; return len(m) })
	try("lookup-slice", func() int { return m[[]int{}] })
	try("lookup-slice-empty-map", func() int { e := map[any]int{}; return e[[]int{}] })
	try("delete-slice", func() int { delete(m, []int{}); return len(m) })
	try("delete-slice-nil-map", func() int { var e map[any]int; delete(e, []int{}); return len(e) })
	try("lookup-slice-nil-map", func() int { var e map[any]int; return e[[]int{}] })
	try("insert-map", func() int { m[map[int]int{}] = 1; return len(m) })
	try("insert-func", func() int { m[func() {}] = 1; return len(m) })
	type WS struct{ S []int }
	try("insert-struct-slice", func() int { m[WS{}] = 1; return len(m) })
	try("insert-array-slice", func() int { m[[1][]int{}] = 1; return len(m) })
	try("lookup-struct-slice-empty-map", func() int { e := map[any]int{}; return e[WS{}] })
	type KI struct{ I any }
	mk := map[KI]int{}
	try("struct-key-iface-ok", func() int { mk[KI{1}] = 1; mk[KI{int64(1)}] = 2; return len(mk) })
	try("struct-key-iface-slice", func() int { mk[KI{[]int{}}] = 1; return len(mk) })
	try("struct-key-iface-slice-lookup", func() int { return mk[KI{[]int{}}] })
	ma := map[[1]any]int{}
	try("array-key-iface-slice", func() int { ma[[1]any{[]int{}}] = 1; return len(ma) })
	// comma-ok and nil key
	_, ok := m[nil]
	println(ok)
	var np *int
	m[np] = 11
	println(m[(*int)(nil)], m[nil])
	x := 0
	m[&x] = 12
	println(m[&x], len(m))
}
