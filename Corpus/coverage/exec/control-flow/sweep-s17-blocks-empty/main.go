package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-012's line): blocks and the empty statement — an empty bare
// block, a lone semicolon between statements, a body of only semicolons
// before the return, a block as a case body, a function whose body ends in
// a block that terminates, and a `break`/`continue` reaching through a
// nested block inside a type switch and a select inside a switch inside a
// for. Expected = gc go1.26.5.

// A14.2
func emptyBlock() int {
	{
	}
	return 1
}

func loneSemicolon() int {
	x := 1
	;
	x++
	return x // 2
}

func bodyOnlySemicolons() int {
	;
	;
	return 2
}

// A14.3
func blockInCase() int {
	x := 1
	r := 0
	switch x {
	case 1:
		{
			r = 1
		}
	}
	return r // 1
}

func blockTerminating() int {
	{
		return 3
	}
}

// A14.4
func unreachableAfterReturn() int {
	x := 4
	return x
	{
		x++
	}
	return x + 100
}

// A11.4
func continueFromTypeSwitchBlock() int {
	n := 0
	for _, v := range []any{1, "a", 2.5, 3} {
		switch v.(type) {
		case string:
			{
				if true {
					continue
				}
			}
		}
		n++
	}
	return n // 3
}

// A11.5
func breakSelectInSwitchInFor() int {
	ch := make(chan int)
	n := 0
	for i := 0; i < 3; i++ {
		switch i {
		case 1:
			select {
			case <-ch:
				break
			default:
				break
			}
			n += 100
		}
		n++
	}
	return n // 103
}

func main() {
	println(emptyBlock(), loneSemicolon(), bodyOnlySemicolons(), blockInCase(), blockTerminating(),
		unreachableAfterReturn(), continueFromTypeSwitchBlock(), breakSelectInSwitchInFor())
}
