package main

func switchNoMatchNoDefault() int {
	result := 1
	switch 2 {
	case 1:
		result = 9
	}
	return result
}

