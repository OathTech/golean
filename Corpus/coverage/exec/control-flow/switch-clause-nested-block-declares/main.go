package main

func switchClauseNestedBlockDeclares() int {
	x := 1
	result := 0
	switch 1 {
	case 1:
		{
			x := 5
			result = result*10 + x
		}
		result = result*10 + x
	}
	return result
}

func main() {
	switchClauseNestedBlockDeclares()
}
