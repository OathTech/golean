package main

var expressionlessSwitchTrace int

func expressionlessSwitchMark(n int, ok bool) bool {
	expressionlessSwitchTrace = expressionlessSwitchTrace*10 + n
	return ok
}

func expressionlessSwitchOrder() int {
	expressionlessSwitchTrace = 0
	result := 0
	switch {
	case expressionlessSwitchMark(1, false):
		result = 10
	case expressionlessSwitchMark(2, true):
		result = 20
	case expressionlessSwitchMark(3, true):
		result = 30
	}
	return expressionlessSwitchTrace*100 + result
}

func main() {
	expressionlessSwitchOrder()
}
