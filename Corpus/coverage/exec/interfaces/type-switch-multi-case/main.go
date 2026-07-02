package main

func typeSwitchMultiCase(x interface{}) int {
	switch x.(type) {
	case int, int32:
		return 1
	case string, bool:
		return 2
	default:
		return 3
	}
}

func typeSwitchMultiCaseSubject() int {
	return typeSwitchMultiCase(int32(4))*10 + typeSwitchMultiCase(true)
}

func main() {
	typeSwitchMultiCaseSubject()
}
