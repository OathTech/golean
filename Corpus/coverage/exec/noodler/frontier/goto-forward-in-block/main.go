// noodler frontier probe — forward goto to a label inside the enclosing for body
package main

// A forward goto whose label sits inside the same nested block (a for
// body), not at function top level (spec#Goto_statements: legal — no
// block is entered, no variable declaration is skipped).
func gotoForwardInBlock() int {
	sum := 0
	for i := 0; i < 4; i++ {
		if i%2 == 1 {
			goto skip
		}
		sum += i
	skip:
		sum += 10
	}
	return sum
}

func main() {}
