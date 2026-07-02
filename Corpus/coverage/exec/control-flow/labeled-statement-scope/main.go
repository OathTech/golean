package main

func labeledStatementScope() int {
	result := 0
	{
		goto L
	}
L:
	result = 1
	return result
}
