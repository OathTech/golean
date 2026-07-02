package main

func labeledEmptyStatement() int {
	result := 1
	goto done
	result = 9
done:
	return result
}
