// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Labelled empty statements (a
// goto target on the closing brace and on a bare semicolon), labelled blocks, labels
// named like a variable / type / function in scope, the same label in two functions and
// in a closure inside its enclosing function, a goto in init; expected = gc go1.26.5.

package main

type pt struct{ v int }

var lab int

func one() int { return 1 }

func init() {
	goto done
	lab = 9
done:
}

func jumpToClosingEmpty() {
	goto end
	lab += 5
end:
}

func jumpToSemicolon() {
	goto end
	lab += 7
end: ;
}

func labelledEmptyStatements() int {
	jumpToClosingEmpty()
	jumpToSemicolon()
	return lab + 100 // 100
}

func labelledBlockAndNames() int {
	n := 0
	goto L
L:
	{
		n++
	}
M:
	for i := 0; i < 3; i++ {
		if i == 1 {
			break M
		}
		n += 10
	}
N:
	switch {
	case true:
		n += 100
		break N
	}
O:
	select {
	default:
		n += 1000
		break O
	}
	x := 1
x:
	for {
		n += x * 10000
		break x
	}
pt:
	for {
		n += 100000
		break pt
	}
one:
	for {
		n += one() * 1000000
		break one
	}
	return n // 1111111
}

func labelInClosureAndOuter() int {
	n := 0
L:
	for {
		func() {
		L:
			for {
				n += 1
				break L
			}
		}()
		n += 10
		break L
	}
	return n + sameLabelTwice() // 11 + 3
}

func labelL1() int {
	n := 0
L:
	for {
		n++
		break L
	}
	return n
}

func labelL2() int {
	n := 0
L:
	for {
		n += 2
		break L
	}
	return n
}

func sameLabelTwice() int { return labelL1() + labelL2() }

func main() {
	println("labelledEmptyStatements", labelledEmptyStatements())
	println("labelledBlockAndNames", labelledBlockAndNames())
	println("labelInClosureAndOuter", labelInClosureAndOuter())
}
