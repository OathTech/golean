package main

// S14 sweep (lane sweep/s14-map-iter, 2026-10-27; members BUG-005, BUG-088):
// VALUE KINDS at the pick's self-normalization guard (every pick validates
// the live entries at the range key/value types and refuses by name
// otherwise — `stuck` on a legal program would be a finding): boxed values
// of every kind in map[any]any, slices, structs, error values, func values,
// pointers read through, and nil values of every nilable kind, each with a
// mutation during the range.

type pt struct{ a, b int }

// any-any-mutated: boxed struct / pointer / map / slice values, the current
// key deleted and a struct-keyed string inserted at the first production.
// Strict cut: four productions' kinds counted, the created at most once.
func s14AnyAnyMutated() int {
	m := map[any]any{1: pt{1, 2}, "s": new(int), true: map[int]int{1: 1}, 2.5: []int{1, 2}}
	n, kinds, created := 0, 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		switch v.(type) {
		case pt:
			kinds += 1
		case *int:
			kinds += 10
		case map[int]int:
			kinds += 100
		case []int:
			kinds += 1000
		case string:
			created++
		}
		if n == 1 {
			delete(m, k)
			m[pt{9, 9}] = "new"
		}
	}
	if created > 1 {
		return -5
	}
	return kinds*10 + len(m)
}

// slice-values-replaced: the unreached entries' slices replaced by longer
// literals at every production (read live: 1 + 3 + 3).
func s14SliceValuesReplaced() int {
	m := map[int][]int{1: {1}, 2: {2}, 3: {3}}
	n, total := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		total += len(v)
		for i := 1; i <= 3; i++ {
			if i != k {
				m[i] = []int{i, i, i}
			}
		}
	}
	return n*1000 + total*100 + len(m[1]) + len(m[2]) + len(m[3])
}

// struct-values-replaced: the unreached entries' struct values replaced at
// the first production; the later productions read {7, 7}. Strict cut: the
// sum minus the first value is 154.
func s14StructValuesReplaced() int {
	m := map[int]pt{1: {1, 1}, 2: {2, 2}, 3: {3, 3}}
	n, sum, first := 0, 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v.a*10 + v.b
		if n == 1 {
			first = v.a*10 + v.b
			for i := 1; i <= 3; i++ {
				if i != k {
					m[i] = pt{7, 7}
				}
			}
		}
	}
	return n*1000 + (sum - first)
}

type myErr struct{ code int }

func (e myErr) Error() string { return "myErr" }

// error-values: a defined error type and a nil error as values; the current
// key deleted and a new error inserted at the first production. Strict cut:
// the three start values' codes and nils, the created at most once.
func s14ErrorValues() int {
	m := map[string]error{"a": myErr{1}, "b": nil, "c": myErr{3}}
	n, codes, nils, created := 0, 0, 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		if v == nil {
			nils++
		} else if e, ok := v.(myErr); ok {
			if e.code == 4 {
				created++
			} else {
				codes += e.code
			}
		}
		if n == 1 {
			delete(m, k)
			m["d"] = myErr{4}
		}
	}
	if created > 1 {
		return -5
	}
	return codes*100 + nils*10 + len(m)
}

// func-values: func values called at their production, the current replaced.
func s14FuncValues() int {
	m := map[int]func() int{1: func() int { return 1 }, 2: func() int { return 2 }, 3: func() int { return 3 }}
	n, sum := 0, 0
	for k, f := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += f()
		m[k] = func() int { return 10 }
	}
	return n*1000 + sum*10 + m[1]() + m[2]() + m[3]() - 29
}

// pointer-values-through: pointer values whose pointees are rewritten
// through the pointers at every production (the entries untouched; the
// production reads the live pointee). Strict cut: sum minus the first is 200.
func s14PointerValuesThrough() int {
	a, b, c := 1, 2, 3
	m := map[int]*int{1: &a, 2: &b, 3: &c}
	n, sum, first := 0, 0, 0
	for _, p := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += *p
		if n == 1 {
			first = *p
		}
		a, b, c = 100, 100, 100
	}
	return n*1000 + (sum - first)
}

// nil-value-kinds: nil values of every nilable kind (map, slice, pointer,
// func, chan, any, error) ranged with a delete of the current key.
func s14NilValueKinds() int {
	m1 := map[int]map[int]int{1: nil, 2: {2: 2}}
	m2 := map[int][]int{1: nil, 2: {2}}
	m3 := map[int]*int{1: nil, 2: new(int)}
	m4 := map[int]func() int{1: nil, 2: func() int { return 2 }}
	m5 := map[int]chan int{1: nil, 2: make(chan int)}
	m6 := map[int]any{1: nil, 2: pt{2, 2}}
	m7 := map[int]error{1: nil}
	nils := 0
	for k, v := range m1 {
		if v == nil {
			nils++
		}
		delete(m1, k)
	}
	for k, v := range m2 {
		if v == nil {
			nils++
		}
		delete(m2, k)
	}
	for k, v := range m3 {
		if v == nil {
			nils++
		}
		delete(m3, k)
	}
	for k, v := range m4 {
		if v == nil {
			nils++
		}
		delete(m4, k)
	}
	for k, v := range m5 {
		if v == nil {
			nils++
		}
		delete(m5, k)
	}
	for k, v := range m6 {
		if v == nil {
			nils++
		}
		delete(m6, k)
	}
	for k, v := range m7 {
		if v == nil {
			nils++
		}
		delete(m7, k)
	}
	return nils*100 + len(m1) + len(m2) + len(m3) + len(m4) + len(m5) + len(m6) + len(m7)
}

func main() {
	println(s14AnyAnyMutated())
	println(s14SliceValuesReplaced())
	println(s14StructValuesReplaced())
	println(s14ErrorValues())
	println(s14FuncValues())
	println(s14PointerValuesThrough())
	println(s14NilValueKinds())
}
