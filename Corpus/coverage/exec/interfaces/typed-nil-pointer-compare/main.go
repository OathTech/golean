package main

type nilCompareA struct{}
type nilCompareB struct{}

func typedNilPointerCompare() int {
	var a1 *nilCompareA
	var a2 *nilCompareA
	var b *nilCompareB
	var x any = a1
	var y any = a2
	var z any = b
	score := 0
	if x == y {
		score += 1
	}
	if x != z {
		score += 10
	}
	if x != nil {
		score += 100
	}
	return score
}

func main() {
	typedNilPointerCompare()
}
