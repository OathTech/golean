package main

func channelNilValues() int {
	var ch chan int
	score := len(ch)*100 + cap(ch)*10
	if ch == nil {
		score += 1
	}
	return score
}

func main() {
	channelNilValues()
}
