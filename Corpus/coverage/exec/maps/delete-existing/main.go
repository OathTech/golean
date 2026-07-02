package main

func mapDeleteExisting() int {
	m := map[int]int{1: 10, 2: 20}
	delete(m, 1)
	_, ok := m[1]
	score := len(m)*100 + m[1]*10 + m[2]
	if !ok {
		score += 1
	}
	return score
}

func main() {
	mapDeleteExisting()
}
