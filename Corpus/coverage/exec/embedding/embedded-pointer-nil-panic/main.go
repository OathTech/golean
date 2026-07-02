package main

type embeddedNilInner struct {
	x int
}

type embeddedNilOuter struct {
	*embeddedNilInner
}

func embeddedPointerNilPanic() int {
	var o embeddedNilOuter
	return o.x
}
