package main

func builtinMinMaxStrings() int {
	score := 0
	if min("go", "ga") == "ga" {
		score += 1
	}
	if max("go", "ga") == "go" {
		score += 10
	}
	return score
}

func main() {
	builtinMinMaxStrings()
}
