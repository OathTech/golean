package main

// Type switch with an INIT statement (its scope covers the whole switch).

func typeSwitchInitStmt() int {
	switch x := any(4); v := x.(type) {
	case int:
		return v + 10
	default:
		return 0
	}
}
