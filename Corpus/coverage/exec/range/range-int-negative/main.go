package main

func rangeIntNegative() int {
	count := 0
	for i := range -3 {
		count += i + 1
	}
	return count
}
