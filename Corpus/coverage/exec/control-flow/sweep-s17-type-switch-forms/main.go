package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-024's line): type switches at the guard and placement shapes the
// corpus did not hold — a parenthesised guard operand with and without a
// binding, an init beside a binding, an empty body, `case nil` first, a
// type switch nested in a clause, inside a select case, with `continue`
// through a loop, and inside a closure. Expected = gc go1.26.5.

func mk() any { return 7 }

// A17.2
func parenGuard() int {
	var v any = 3
	r := 0
	switch (v).(type) {
	case int:
		r = 1
	}
	return r // 1
}

func parenGuardBinding() int {
	var v any = 4
	r := 0
	switch x := (v).(type) {
	case int:
		r = x
	}
	return r // 4
}

// A17.3
func initAndBinding() int {
	r := 0
	switch x := mk(); y := x.(type) {
	case int:
		r = y
	}
	return r // 7
}

// A17.4
func emptyNoBinding() int {
	var v any = "s"
	switch v.(type) {
	}
	return 1
}

// A17.5
func nilFirst(k int) int {
	var v any
	if k != 0 {
		v = k
	}
	switch v.(type) {
	case nil:
		return 1
	case int:
		return 2
	}
	return 0
}

// A17.6
func nestedTypeSwitch() int {
	var v any = 5
	var w any = "ab"
	r := 0
	switch x := v.(type) {
	case int:
		switch y := w.(type) {
		case string:
			r = x + len(y)
		}
	}
	return r // 7
}

func typeSwitchInSelect() int {
	ch := make(chan any, 1)
	ch <- 9
	r := 0
	select {
	case v := <-ch:
		switch t := v.(type) {
		case int:
			r = t
		}
	}
	return r // 9
}

func typeSwitchContinue() int {
	n := 0
	for _, v := range []any{1, "a", 2} {
		switch v.(type) {
		case string:
			continue
		}
		n++
	}
	return n // 2
}

// A17.8
func typeSwitchInClosure() int {
	f := func(v any) int {
		switch t := v.(type) {
		case int:
			return t
		case string:
			return len(t)
		}
		return -1
	}
	return f(3)*100 + f("ab")*10 + f(nil) // 300 + 20 - 1 = 319
}

func main() {
	println(parenGuard(), parenGuardBinding(), initAndBinding(), emptyNoBinding(), nilFirst(0), nilFirst(1),
		nestedTypeSwitch(), typeSwitchInSelect(), typeSwitchContinue(), typeSwitchInClosure())
}
