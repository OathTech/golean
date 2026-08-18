package main

// spec#Composite_literals block Composite_literals-2-0f327af4: a
// composite literal using the TypeName form between an `if` keyword
// and the block's opening brace must be parenthesized to resolve the
// parsing ambiguity. Both spellings the spec shows — parenthesizing
// the literal, or parenthesizing the whole condition — are legal and
// denote the same comparison. Expected: for T{a,b,c} == {4,5,6},
// x == T{a,b,c}[i] iff x equals element i; both forms agree.

type cpaT [3]int

func complitParenForms(x, i int) int {
	a, b, c := 4, 5, 6
	score := 0
	if x == (cpaT{a, b, c}[i]) {
		score += 1
	}
	if (x == cpaT{a, b, c}[i]) {
		score += 10
	}
	return score // 11 when equal, 0 when not: the two forms never disagree
}

func main() {
	complitParenForms(5, 1)
}
