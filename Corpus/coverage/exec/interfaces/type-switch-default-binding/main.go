package main

func typeSwitchDefaultBinding(x interface{}) int {
	switch v := x.(type) {
	case int:
		return v
	default:
		return 7
	}
}

func typeSwitchDefaultBindingSubject() int {
	return typeSwitchDefaultBinding("x")
}

func main() {
	typeSwitchDefaultBindingSubject()
}
