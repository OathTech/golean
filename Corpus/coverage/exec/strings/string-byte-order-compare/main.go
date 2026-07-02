package main

func stringByteOrderCompare() int {
	score := 0
	if "a\xff" > "a\u00fe" {
		score += 1
	}
	if "go" < "go!" {
		score += 10
	}
	if "\x00" < "\x01" {
		score += 100
	}
	return score
}

func main() {
	stringByteOrderCompare()
}
