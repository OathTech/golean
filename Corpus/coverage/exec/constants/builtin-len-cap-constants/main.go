package main

func builtinLenCapConstants() int {
	const stringBytes = len("hé")
	const arrayLen = len([3]int{})
	const arrayCap = cap([...]int{1, 2, 3, 4})
	return stringBytes*100 + arrayLen*10 + arrayCap
}
