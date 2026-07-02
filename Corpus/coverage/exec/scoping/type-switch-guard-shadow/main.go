package main

func typeSwitchGuardShadow() int {
	var value any = 7
	v := 100
	result := 0
	switch v := value.(type) {
	case int:
		result = v
	default:
		result = 1
	}
	return v + result
}

func main() {
	typeSwitchGuardShadow()
}
