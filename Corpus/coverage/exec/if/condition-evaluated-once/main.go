package main

func ifConditionEvaluatedOnce() int {
	calls := 0
	cond := func() bool {
		calls++
		return true
	}
	if cond() {
		return calls*10 + 1
	}
	return calls * 10
}

func main() {
	ifConditionEvaluatedOnce()
}
