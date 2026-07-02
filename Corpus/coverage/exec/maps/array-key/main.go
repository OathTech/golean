package main

func mapArrayKey() int {
	key := [2]int{1, 2}
	m := map[[2]int]int{
		key: 7,
	}
	return len(m)*100 + m[[2]int{1, 2}]
}

func main() {
	mapArrayKey()
}
