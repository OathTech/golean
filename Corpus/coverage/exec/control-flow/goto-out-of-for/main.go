package main

func gotoOutOfFor() int {
	result := 0
	for i := 0; i < 5; i++ {
		result = result*10 + i
		if i == 2 {
			goto done
		}
	}
	result = 99
done:
	return result
}
