package main

// Labeled break interplay with type switches: (a) `break L` from inside a
// type-switch clause exits the enclosing labeled LOOP (not just the
// switch); (b) a LABELED type switch is itself a break target.

func typeSwitchBreakOutOfLoop() int {
	total := 0
loop:
	for i := 0; i < 3; i++ {
		var x any = i
		switch x.(type) {
		case int:
			total += 10
			break loop
		}
	}
	return total
}

func typeSwitchLabeledSelf() int {
	var x any = "go"
	total := 0
sw:
	switch v := x.(type) {
	case string:
		total += len(v)
		if total > 0 {
			break sw
		}
		total += 100
	default:
		total = 9
	}
	return total
}
