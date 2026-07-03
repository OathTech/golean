package main

func rangeFuncZeroValueIterator() int {
	calls := 0
	body := 0
	seq := func(yield func() bool) {
		for i := 0; i < 3; i++ {
			calls++
			if !yield() {
				return
			}
		}
	}
	for range seq {
		body++
	}
	return calls*10 + body
}

func rangeFuncTwoValueIterator() int {
	seq := func(yield func(int, string) bool) {
		if !yield(2, "go") {
			return
		}
		if !yield(5, "lean") {
			return
		}
	}
	total := 0
	for k, v := range seq {
		total = total*100 + k*10 + len(v)
	}
	return total
}

func rangeFuncZeroYieldedValues() int {
	seq := func(yield func(int, string) bool) {
		if !yield(0, "") {
			return
		}
		if !yield(3, "") {
			return
		}
	}
	count := 0
	total := 0
	for k, v := range seq {
		count++
		total += k + len(v)
	}
	return count*100 + total
}

func rangeFuncNoYield() int {
	called := 0
	seq := func(yield func(int) bool) {
		_ = yield
		called = 7
	}
	sum := 0
	for v := range seq {
		sum += v
	}
	return called*10 + sum
}

func rangeFuncBreakDeferTrace() int {
	trace := 0
	seq := func(yield func(int) bool) {
		defer func() {
			trace = trace*10 + 9
		}()
		for i := 1; i <= 3; i++ {
			trace = trace*10 + i
			if !yield(i) {
				trace = trace*10 + 7
				return
			}
			trace = trace*10 + 8
		}
	}
	for v := range seq {
		if v == 2 {
			break
		}
	}
	return trace
}

func rangeFuncPanicPropagation() int {
	seq := func(yield func(int) bool) {
		if !yield(1) {
			return
		}
		panic("iterator boom")
	}
	for v := range seq {
		_ = v
	}
	return 0
}

func rangeFuncIgnoredFalsePanic() int {
	seq := func(yield func(int) bool) {
		yield(1)
		yield(2)
		yield(3)
	}
	for v := range seq {
		if v == 2 {
			break
		}
	}
	return 0
}
