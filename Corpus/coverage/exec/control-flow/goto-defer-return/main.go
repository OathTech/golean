package main

func gotoDeferReturn() (result int) {
	defer func() {
		result += 10
	}()
	result = 1
	goto done
	result = 99
done:
	return
}
