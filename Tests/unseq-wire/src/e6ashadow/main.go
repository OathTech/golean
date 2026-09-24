package main

// E6ASHADOW (the Stage E6a audit fix round, 2026-09-24, F2): BLOCK SHADOWING as the R1 declaration
// environment's POSITIVE CONTROL — `x` declared `int` in the function block and `string` in the
// inner block; the outer sweep `s[x] + wit(1)` and the inner `int(x[1]) + wit(2)` are each an
// `unseq` graph whose `x` is annotated with the declaration IN SCOPE at that statement. The
// frontend's OWN lowering only (NATIVE). Two mutants ride on it: `mut-local-shadow-other-decl`
// (the inner graph's `x` annotated `int`, the OUTER declaration's type — the residual the E6a
// tip's flat table stated and passed) and `mut-local-out-of-scope` (the outer graph names `z`,
// declared only AFTER the inner block — in the function, not in scope). Singleton {108} with the
// output `wit 1` `wit 2`: 7 + 1 + 'b' 98 + 2; z is 0.
func wit(x int) int { println("wit", x); return x }

func e6ashadow() int {
	x := 0
	s := []int{7}
	r := s[x] + wit(1)
	{
		x := "ab"
		r += int(x[1]) + wit(2)
	}
	z := 0
	return r + z
}

func main() { println(e6ashadow()) }
