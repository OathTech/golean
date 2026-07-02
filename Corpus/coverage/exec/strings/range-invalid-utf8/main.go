package main

func rangeInvalidUTF8() int {
	s := string([]byte{65, 255, 195, 169})
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
