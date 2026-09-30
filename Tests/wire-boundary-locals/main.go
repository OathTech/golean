// Tests/wire-boundary-locals/main.go — the B6 numeric-locals fixture for
// scripts/check-wire-boundary (2026-09-30; design note
// docs/2026-09-30_numeric-locals-design.md D5). Lowered FRESH by the gate with the
// production frontend; every declaration shape the decoder checks (c1–c5) has a
// witness here, and the gate's Python mutants forge one field at a time on this
// wire and expect the decoder's refusal BY NAME through the real CLI:
//
//   - `shadow`: an outer `x` and an inner `x` (two objects, two declaration ids)
//     with a reference to each — the c4 agreement control swaps the inner
//     reference's index to the outer's declaration;
//   - `capture`: a lifted literal whose capture pointer `x$cap` is a `capture`
//     entry of the lifted function's table;
//   - `named` / `reuse`: a named result and a `:=` that reuses `err` (a use, not
//     a declaration);
//   - `iter`: a range key/value pair (`keyLocal` / `valLocal`) and a type-switch
//     clause binder.
//
// The program's own behaviour is incidental (it prints a few integers); it is not
// a differential row.
package main

func shadow(n int) int {
	x := n
	if n > 1 {
		x := x * 2
		println(x)
	}
	return x
}

func capture() func() int {
	x := 3
	return func() int { x++; return x }
}

func named(a int) (r int, err error) {
	r = a + 1
	if a > 5 {
		_, err = 0, nil
	}
	return
}

func iter(xs []int, v any) int {
	s := 0
	for i, x := range xs {
		s += i * x
	}
	switch t := v.(type) {
	case int:
		s += t
	case bool:
		if t {
			s++
		}
	}
	return s
}

func main() {
	println(shadow(2))
	f := capture()
	println(f() + f())
	r, _ := named(7)
	println(r)
	println(iter([]int{1, 2, 3}, 4))
}
