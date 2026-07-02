package main

func gotoOutOfSelect() int {
	result := 1
	select {
	default:
		result = result*10 + 2
		goto done
	}
	result = 99
done:
	return result
}
