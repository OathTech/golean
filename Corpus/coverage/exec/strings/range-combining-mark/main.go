package main

func rangeCombiningMark() int {
	s := "e\u0301"
	count := 0
	indexSum := 0
	runeSum := 0
	for i, r := range s {
		count++
		indexSum += i
		runeSum += int(r)
	}
	return count*1000000 + indexSum*1000 + runeSum
}

func main() {
	rangeCombiningMark()
}
