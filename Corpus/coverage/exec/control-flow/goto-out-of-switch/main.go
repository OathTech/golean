package main

func gotoOutOfSwitch() int {
	x := 0
	switch {
	case true:
		x = 1
		goto done
	default:
		x = 9
	}
	x = 99
done:
	return x
}
