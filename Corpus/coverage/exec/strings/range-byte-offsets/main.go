package main

func rangeByteOffsets() int {
	s := string([]byte{104, 195, 169, 108})
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
