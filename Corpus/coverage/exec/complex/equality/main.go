package main

func complexEquality() int {
	a := complex(1.0, 2.0)
	b := complex(1.0, 2.0)
	c := complex(2.0, 1.0)
	score := 0
	if a == b {
		score += 1
	}
	if a != c {
		score += 10
	}
	return score
}

func main() {
	complexEquality()
}
