package main

// DC01 neighbourhood: must-stay-UNEQUAL controls — distinct allocations
// with equal contents are distinct pointers (and distinct map keys) even
// though the VALUES compare equal. A canonical-location identity that
// over-merged (erasing anything but the static spelling) would flip these.

type pair struct{ X int }

func distinctStructs() bool {
	a := pair{X: 7}
	c := pair{X: 7}
	return &a.X == &c.X
}

func distinctNew() bool {
	p := new(int)
	q := new(int)
	return p == q
}

func distinctMapKeys() int {
	a := pair{X: 7}
	c := pair{X: 7}
	m := map[*int]int{&a.X: 1}
	m[&c.X] = 2
	return 10*len(m) + m[&a.X]
}

func valuesEqualPointersNot() int {
	a := pair{X: 7}
	c := pair{X: 7}
	score := 0
	if a == c {
		score += 1
	}
	if &a == &c {
		score += 10
	}
	return score
}

func main() { println(distinctStructs(), distinctNew(), distinctMapKeys(), valuesEqualPointersNot()) }
