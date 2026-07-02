package main

func f() {
	goto L
	if true {
	L:
		return
	}
}
