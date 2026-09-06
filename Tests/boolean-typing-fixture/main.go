package main

func Argument(b bool) (result bool) {
	result = b && !false
	return
}

func Shadow() (result bool) {
	x := true
	{
		x := !x
		result = x
	}
	result = result && x
	return
}

func Branches() (result bool) {
	var b bool
	if b {
		result = true
		return
	} else {
		result = false
		return
	}
}

func Zero() (result bool) {
	var zero bool
	result = result || zero
	return
}
