package main

func targetEvalBeforeCallPair(s []int) (int, int) {
	s[0] = 9
	return 1, 2
}

func multiAssignTargetEvalBeforeCall() int {
	s := []int{0, 0}
	i := 0
	i, s[i] = targetEvalBeforeCallPair(s)
	return i*100 + s[0]*10 + s[1]
}

func main() {
	multiAssignTargetEvalBeforeCall()
}
